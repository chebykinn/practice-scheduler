#include <sys/cdefs.h>

#include "opt_hwpmc_hooks.h"
#include "opt_sched.h"
#include "opt_kdtrace.h"

#include <sys/param.h>
#include <sys/systm.h>
#include <sys/cpuset.h>
#include <sys/kernel.h>
#include <sys/ktr.h>
#include <sys/sdt.h>
#include <sys/lock.h>
#include <sys/kthread.h>
#include <sys/mutex.h>
#include <sys/proc.h>
#include <sys/resourcevar.h>
#include <sys/sched.h>
#include <sys/smp.h>
#include <sys/sysctl.h>
#include <sys/sx.h>
#include <sys/turnstile.h>
#include <sys/umtx.h>
#include <machine/pcb.h>
#include <machine/smp.h>

/* From 4BSD */
#define	ESTCPULIM(e) \
    min((e), INVERSE_ESTCPU_WEIGHT * (NICE_WEIGHT * (PRIO_MAX - PRIO_MIN) - \
    RQ_PPQ) + INVERSE_ESTCPU_WEIGHT - 1)
#ifdef SMP
#define	INVERSE_ESTCPU_WEIGHT	(8 * smp_cpus)
#else
#define	INVERSE_ESTCPU_WEIGHT	8	/* 1 / (priorities per estcpu level). */
#endif
#define	NICE_WEIGHT		1	/* Priorities per nice level. */

#define	TS_NAME_LEN (MAXCOMLEN + sizeof(" td ") + sizeof(__XSTRING(UINT_MAX)))

struct td_sched {
	struct runq	*ts_runq;   // Thread's runq
	int		ts_cpu_ticks;   // Ticks of cpu time.
	int		ts_sleeptime;   // Seconds of sleeping.
	int		ts_slice;       // Remaining part of time slice.
	int		ts_flags;       // Sched flags
#ifdef KTR
	char		ts_name[TS_NAME_LEN];
#endif
};

/* flags kept in td_flags */
#define TDF_DIDRUN	TDF_SCHED0	/* thread actually ran. */
#define TDF_BOUND	TDF_SCHED1	/* Bound to one CPU. */
#define	TDF_SLICEEND	TDF_SCHED2	/* Thread time slice is over. */

/* flags kept in ts_flags */
#define	TSF_AFFINITY	0x0001		/* Has a non-"full" CPU set. */

#define SKE_RUNQ_PCPU(ts)						\
    ((ts)->ts_runq != 0 && (ts)->ts_runq != &runq )

#define	THREAD_CAN_SCHED(td, cpu)	\
    CPU_ISSET((cpu), &(td)->td_cpuset->cs_mask )

static struct td_sched td_sched0;
struct mtx sched_lock;

static int	realstathz = 127; // stathz is sometimes 0 and run off of hz.
static int	sched_td_count;	// Total runnable threads in the system.
static int	sched_slice = 12; // Thread run time before rescheduling.

static void	init_runqs(void);
static void	sched_setup(void *not_used);
static void	usched_set_priority(struct thread *td, u_char prio);
static void	usched_try_resched(struct thread *td);
static void	usched_update_priority(struct thread *td);
static void	usched_reset_priority(struct thread *td);
static void	usched_reset_priority_thread(struct thread *td);
#ifdef SMP
static int	usched_assign_cpu(struct thread *td);
#endif

SYSINIT(sched_setup, SI_SUB_RUN_QUEUE, SI_ORDER_FIRST, sched_setup, NULL);

static void sched_initticks(void *dummy);
SYSINIT(sched_initticks, SI_SUB_CLOCKS, SI_ORDER_THIRD, sched_initticks,
    NULL);

/*
 * Global run queue.
 */
static struct runq runq;
#ifdef SMP
/*
 * Per-CPU run queues
 */
static struct runq runq_pcpu[MAXCPU];
long runq_length[MAXCPU];

static cpuset_t idle_cpus_mask;
#endif

struct pcpuidlestat {
	u_int idlecalls;
	u_int oldidlecalls;
};
static DPCPU_DEFINE(struct pcpuidlestat, idlestat);
/*
 * Print the threads waiting on a run-queue.
 */
static void runq_print(struct runq *rq) {
	struct rqhead *rqh;
	struct thread *td;
	int pri;
	int j;
	int i;

	for (i = 0; i < RQB_LEN; i++) {
		printf("\t\trunq bits %d 0x%zx\n", i, rq->rq_status.rqb_bits[i]);
		for (j = 0; j < RQB_BPW; j++){
			if( rq->rq_status.rqb_bits[i] & (1ul << j)) {
				pri = j + (i << RQB_L2BPW);
				rqh = &rq->rq_queues[pri];
				TAILQ_FOREACH(td, rqh, td_runq) {
					printf("\t\t\ttd %p(%s) priority %d rqindex %d pri %d\n",
						td, td->td_name, td->td_priority,
						td->td_rqindex, pri);
				}
			}
		}
	}
}

/*
 * Scheduler control interface
 */
void sched_control(int signum, struct thread *td){
	switch(signum){
		case SIG_SCHEDSWTCH:
			maybe_preempt(td);
		break;

		case SIG_SCHEDRUNQ:
			runq_print(&runq);
		break;

		case SIG_SCHEDCMD:
			printf("[uSched] Entering cmd");
		break;
	}
}


static void init_runqs(void) {
	// If we have multiple CPUs, then we will use one runq per CPU
#ifdef SMP
	int i;

	for (i = 0; i < MAXCPU; ++i)
		runq_init(&runq_pcpu[i]);
#endif

	runq_init(&runq);
}


/*
 * Increase running threads counter
 */
static __inline void usched_load_cnt_inc(void) {
	sched_td_count++;
}

/*
 * Decrease running threads counter
 */
static __inline void usched_load_cnt_dec(void) {
	sched_td_count--;
}

/*
 * Switch to given thread if it has bigger priority than current thread
 */
static void usched_try_resched(struct thread *td) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);

	if( td->td_priority < curthread->td_priority )
		curthread->td_flags |= TDF_NEEDRESCHED;
}

/*
 * If preemption is enabled in kernel, check priority of current thread
 * and switch to given thread
 * This function is called when new thread is added, and checks if we can
 * immediately switch to this thread
 */
int maybe_preempt(struct thread *td) {
#ifdef PREEMPTION
	struct thread *ctd;
	int cpri, pri;

	ctd = curthread;
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	pri = td->td_priority;
	cpri = ctd->td_priority;
	if( panicstr != NULL || pri >= cpri || cold || TD_IS_INHIBITED(ctd) )
		return (0);
#ifndef FULL_PREEMPTION
	if( pri > PRI_MAX_ITHD && cpri < PRI_MIN_IDLE )
		return (0);
#endif

	// Check critical area before switch
	if( ctd->td_critnest > 1 ) {
		ctd->td_owepreempt = 1;
		return (0);
	}

	MPASS(ctd->td_lock == td->td_lock);
	MPASS(TD_ON_RUNQ(td));
	TD_SET_RUNNING(td);
	mi_switch(SW_INVOL | SW_PREEMPT | SWT_PREEMPT, td);

	spinlock_enter();
	thread_unlock(ctd);
	thread_lock(td);
	spinlock_exit();
	return (1);
#else
	return (0);
#endif
}

/*
 * 4BSD Scheduler formula
 */
/* calculations for digital decay to forget 90% of usage in 5*loadav sec */
#define	loadfactor(loadav)	(2 * (loadav) )
#define	decay_cpu(loadfac, cpu)	(((loadfac) * (cpu)) / ((loadfac) + FSCALE) )

static void usched_update_priority(struct thread *td) {
	struct td_sched *ts;
	fixpt_t loadfac;
	unsigned int newcpu;

	ts = td->td_sched;
	loadfac = loadfactor(averunnable.ldavg[0]);
	if( ts->ts_sleeptime > 5 * loadfac )
		td->td_estcpu = 0;
	else {
		newcpu = td->td_estcpu;
		ts->ts_sleeptime--;
		while( newcpu && --ts->ts_sleeptime )
			newcpu = decay_cpu(loadfac, newcpu);
		td->td_estcpu = newcpu;
	}
}

/*
 * Calculate user mode priority
 */
static void usched_reset_priority(struct thread *td) {
	unsigned int newpriority;

	if( td->td_pri_class == PRI_TIMESHARE ) {
		newpriority = PUSER + td->td_estcpu / INVERSE_ESTCPU_WEIGHT +
			NICE_WEIGHT * (td->td_proc->p_nice - PRIO_MIN);
		newpriority = min(max(newpriority, PRI_MIN_TIMESHARE),
			PRI_MAX_TIMESHARE);
		sched_user_prio(td, newpriority);
	}
}

/*
 * Update the thread's priority when the associated process's user
 * priority changes.
 */
static void usched_reset_priority_thread(struct thread *td) {
	// Used only for time sharing class
	if( td->td_priority < PRI_MIN_TIMESHARE ||
		td->td_priority > PRI_MAX_TIMESHARE )
		return;

	usched_try_resched(td);

	sched_prio(td, td->td_user_pri);
}

/*
 * Adjust the priority of a thread.
 */
static void usched_set_priority(struct thread *td, u_char prio) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	if( td->td_priority == prio )
		return;
	td->td_priority = prio;
	if( TD_ON_RUNQ(td) && td->td_rqindex != (prio / RQ_PPQ) ){
		sched_rem(td);
		sched_add(td, SRQ_BORING);
	}
}

#ifdef SMP
/*
 * Select CPU
 */
static int usched_assign_cpu(struct thread *td) {
	int best, cpu;

	mtx_assert(&sched_lock, MA_OWNED);

	if( THREAD_CAN_SCHED(td, td->td_lastcpu) )
		best = td->td_lastcpu;
	else
		best = NOCPU;
	CPU_FOREACH(cpu) {
		if( !THREAD_CAN_SCHED(td, cpu) )
			continue;

		if( best == NOCPU )
			best = cpu;
		else if( runq_length[cpu] < runq_length[best] )
			best = cpu;
	}
	KASSERT(best != NOCPU, ("no valid CPUs"));

	return (best);
}
#endif

/*
 * Initialize run queues and schedule first thread
 */
static void sched_setup(void *dummy) {

	init_runqs();

	usched_load_cnt_inc();
}

/*
 * This routine determines time constants after stathz and hz are setup.
 */
static void sched_initticks(void *dummy) {

	realstathz = stathz ? stathz : hz;
	sched_slice = realstathz / 10;	/* ~100ms */
	hogticks = imax(1, (2 * hz * sched_slice + realstathz / 2) / realstathz);
}


/*
 * General scheduling info.
 *
 * sched_load:
 *	Total runnable non-ithread threads in the system.
 *
 * sched_runnable:
 *	Runnable threads for this processor.
 */

int sched_load(void) {
	return (sched_td_count);
}

/* Convert sched_slice from stathz to hz. */
int sched_rr_interval(void) {
	return (imax(1, (sched_slice * hz + realstathz / 2) / realstathz));
}

int sched_runnable(void) {
#ifdef SMP
	return runq_check(&runq) + runq_check(&runq_pcpu[PCPU_GET(cpuid)]);
#else
	return runq_check(&runq);
#endif
}

/*
 * Charge child's scheduling CPU usage to parent.
 */
void sched_exit(struct proc *p, struct thread *td) {
	PROC_LOCK_ASSERT(p, MA_OWNED);
	sched_exit_thread(FIRST_THREAD_IN_PROC(p), td);
}

void sched_fork(struct thread *td, struct thread *childtd) {
	sched_fork_thread(td, childtd);
}

void sched_fork_exit(struct thread *td) {
	td->td_oncpu = PCPU_GET(cpuid);
	sched_lock.mtx_lock = (uintptr_t)td;
	lock_profile_obtain_lock_success(&sched_lock.lock_object,
		0, 0, __FILE__, __LINE__);
	THREAD_LOCK_ASSERT(td, MA_OWNED | MA_NOTRECURSED);
}

/*
 * Set priority class
 */
void sched_class(struct thread *td, int class) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	td->td_pri_class = class;
}

void sched_nice(struct proc *p, int nice) {
	struct thread *td;

	PROC_LOCK_ASSERT(p, MA_OWNED);
	p->p_nice = nice;
	FOREACH_THREAD_IN_PROC(p, td) {
		thread_lock(td);
		usched_reset_priority(td);
		usched_reset_priority_thread(td);
		thread_unlock(td);
	}
}

/*
 * Threads are switched in and out, block on resources, have temporary
 * priorities inherited from their procs, and use up cpu time.
 */
void sched_exit_thread(struct thread *td, struct thread *child) {
	thread_lock(td);
	td->td_estcpu = ESTCPULIM(td->td_estcpu + child->td_estcpu);
	thread_unlock(td);
	thread_lock(child);
	if( (child->td_flags & TDF_NOLOAD) == 0 )
		usched_load_cnt_dec();
	thread_unlock(child);
}

void sched_fork_thread(struct thread *td, struct thread *childtd) {
	struct td_sched *ts;

	childtd->td_estcpu = td->td_estcpu;
	childtd->td_lock = &sched_lock;
	childtd->td_cpuset = cpuset_ref(td->td_cpuset);
	childtd->td_priority = childtd->td_base_pri;
	ts = childtd->td_sched;
	bzero(ts, sizeof(*ts));
	ts->ts_flags |= (td->td_sched->ts_flags & TSF_AFFINITY);
	ts->ts_slice = 1;
}

/*
 * Update a thread's priority when it is lent another thread's
 * priority.
 */
void sched_lend_prio(struct thread *td, u_char prio) {
	td->td_flags |= TDF_BORROWING;
	usched_set_priority(td, prio);
}

void sched_lend_user_prio(struct thread *td, u_char prio) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	td->td_lend_user_pri = prio;
	td->td_user_pri = min(prio, td->td_base_user_pri);
	if( td->td_priority > td->td_user_pri )
		sched_prio(td, td->td_user_pri);
	else if( td->td_priority != td->td_user_pri )
		td->td_flags |= TDF_NEEDRESCHED;
}

fixpt_t sched_pctcpu(struct thread *td) {
	return 0;
}

void sched_prio(struct thread *td, u_char prio) {
	u_char oldprio;

	// Set base priority
	td->td_base_pri = prio;

	// Don't lower priority if borrowing
	if( td->td_flags & TDF_BORROWING && td->td_priority < prio )
		return;

	// Update priority
	oldprio = td->td_priority;
	usched_set_priority(td, prio);

	if( TD_ON_LOCK(td) && oldprio != prio )
		turnstile_adjust(td, oldprio);
}

void sched_sleep(struct thread *td, int pri) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	td->td_slptick = ticks;
	td->td_sched->ts_sleeptime = 0;
	if( pri != 0 && PRI_BASE(td->td_pri_class) == PRI_TIMESHARE )
		sched_prio(td, pri);
	if( TD_IS_SUSPENDED(td) || pri >= PSOCK )
		td->td_flags |= TDF_CANSWAP;
}

void sched_switch(struct thread *td, struct thread *newtd, int flags) {
	struct mtx *tmtx;
	struct td_sched *ts;
	struct proc *p;
	int preempted;

	tmtx = NULL;
	ts = td->td_sched;
	p = td->td_proc;

	THREAD_LOCK_ASSERT(td, MA_OWNED);

	// lock thread
	if( td->td_lock != &sched_lock ) {
		mtx_lock_spin(&sched_lock);
		tmtx = thread_lock_block(td);
	}

	// Decrease thread counter
	if( (td->td_flags & TDF_NOLOAD) == 0 )
		usched_load_cnt_dec();

	td->td_lastcpu = td->td_oncpu;

	// Check if thread was moved before end of slice
	preempted = !((td->td_flags & TDF_SLICEEND) || (flags & SWT_RELINQUISH));
	td->td_flags &= ~(TDF_NEEDRESCHED | TDF_SLICEEND);
	td->td_owepreempt = 0;
	td->td_oncpu = NOCPU;

	if( td->td_flags & TDF_IDLETD) {
		TD_SET_CAN_RUN(td);
#ifdef SMP
		CPU_CLR(PCPU_GET(cpuid), &idle_cpus_mask);
#endif
	} else {
		if( TD_IS_RUNNING(td) ) {
			// Put back on the run queue, tell sched_add if thread was moved
			int flags = preempted ? SRQ_OURSELF | SRQ_YIELDING | SRQ_PREEMPTED
								  : SRQ_OURSELF | SRQ_YIELDING;
			sched_add(td, flags);
		}
	}
	if( newtd ) {
		newtd->td_flags |= TDF_DIDRUN;
		TD_SET_RUNNING(newtd);
		if( (newtd->td_flags & TDF_NOLOAD) == 0 )
			usched_load_cnt_inc();
	} else {
		newtd = choosethread();
		MPASS(newtd->td_lock == &sched_lock);
	}

	if( td != newtd ) {
		lock_profile_release_lock(&sched_lock.lock_object);

		cpu_switch(td, newtd, tmtx != NULL ? tmtx : td->td_lock);
		lock_profile_obtain_lock_success(&sched_lock.lock_object,
			0, 0, __FILE__, __LINE__);
	}

#ifdef SMP
	if( td->td_flags & TDF_IDLETD )
		CPU_SET(PCPU_GET(cpuid), &idle_cpus_mask);
#endif
	sched_lock.mtx_lock = (uintptr_t)td;
	td->td_oncpu = PCPU_GET(cpuid);
	MPASS(td->td_lock == &sched_lock);
}

/*
 * A CPU is entering for the first time or a thread is exiting.
 */
void sched_throw(struct thread *td) {
	if( td == NULL) {
		mtx_lock_spin(&sched_lock);
		spinlock_exit();
		PCPU_SET(switchtime, cpu_ticks());
		PCPU_SET(switchticks, ticks);
	} else {
		lock_profile_release_lock(&sched_lock.lock_object);
		MPASS(td->td_lock == &sched_lock);
	}
	mtx_assert(&sched_lock, MA_OWNED);
	KASSERT(curthread->td_md.md_spinlock_count == 1, ("invalid count"));
	cpu_throw(td, choosethread());
}

/*
 * From 4BSD
 * Restore a thread's priority when priority propagation is
 * over.  The prio argument is the minimum priority the thread
 * needs to have to satisfy other possible priority lending
 * requests.  If the thread's regulary priority is less
 * important than prio the thread will keep a priority boost
 * of prio.
 */
void sched_unlend_prio(struct thread *td, u_char prio) {
	u_char base_pri;

	if( td->td_base_pri >= PRI_MIN_TIMESHARE &&
		td->td_base_pri <= PRI_MAX_TIMESHARE )
		base_pri = td->td_user_pri;
	else
		base_pri = td->td_base_pri;
	if( prio >= base_pri ) {
		td->td_flags &= ~TDF_BORROWING;
		sched_prio(td, base_pri);
	} else
		sched_lend_prio(td, prio);
}

void sched_user_prio(struct thread *td, u_char prio) {

	THREAD_LOCK_ASSERT(td, MA_OWNED);
	td->td_base_user_pri = prio;
	if( td->td_lend_user_pri <= prio )
		return;
	td->td_user_pri = prio;
}

/*
 * Fix priority when returning to user mode
 */
void sched_userret(struct thread *td) {
	KASSERT((td->td_flags & TDF_BORROWING) == 0, ("thread borrowed"));
	if( td->td_priority != td->td_user_pri ) {
		thread_lock(td);
		td->td_priority = td->td_user_pri;
		td->td_base_pri = td->td_user_pri;
		thread_unlock(td);
	}
}

/*
 * Schedule waking thread and count time slept
 */
void sched_wakeup(struct thread *td) {
	struct td_sched *ts;
	int sleep_ticks = 0;
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	ts = td->td_sched;
	sleep_ticks = td->td_slptick;
	td->td_flags &= ~TDF_CANSWAP;

	if( ts->ts_sleeptime > 1) {
		usched_update_priority(td);
		usched_reset_priority(td);
	}
	td->td_slptick = 0;
	// Calculate sleep time
	ts->ts_sleeptime += (ticks - sleep_ticks) << 10;
	ts->ts_slice = sched_slice;
	sched_add(td, SRQ_BORING);
}

void sched_preempt(struct thread *td) {
	thread_lock(td);
	if( td->td_critnest > 1 )
		td->td_owepreempt = 1;
	else
		mi_switch(SW_INVOL | SW_PREEMPT | SWT_PREEMPT, NULL);
	thread_unlock(td);
}

/*
 * Add thread to global queue or to cpu queue
 */
void sched_add(struct thread *td, int flags) {
	cpuset_t tidlemsk;
	struct td_sched *ts;
	u_int cpu, cpuid;
	int single_cpu = 0;

	ts = td->td_sched;
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	KASSERT((TD_CAN_RUN(td) || TD_IS_RUNNING(td)), "bad thread state");
	KASSERT(td->td_flags & TDF_INMEM, ("thread swapped out"));

	if( td->td_lock != &sched_lock) {
		mtx_lock_spin(&sched_lock);
		thread_lock_set(td, &sched_lock);
	}
	TD_SET_RUNQ(td);

	if(    smp_started && (td->td_pinned != 0
		|| td->td_flags & TDF_BOUND
		|| ts->ts_flags & TSF_AFFINITY) ) {
		if( td->td_pinned != 0 )
			cpu = td->td_lastcpu;
		else if( td->td_flags & TDF_BOUND ) {
			// Get CPU from bound runq
			KASSERT(SKE_RUNQ_PCPU(ts), ("bound td_sched not on cpu runq"));
			cpu = ts->ts_runq - &runq_pcpu[0];
		}else{
			// Find CPU
			cpu = usched_assign_cpu(td);
		}
		ts->ts_runq = &runq_pcpu[cpu];
		single_cpu = 1;
		CTR1(KTR_SCHED, "Added thread to runq on cpu: %d", cpu);
	} else {
		cpu = NOCPU;
		ts->ts_runq = &runq;
		CTR0(KTR_SCHED, "Added thread to global runq");
	}

	cpuid = PCPU_GET(cpuid);
	if( !single_cpu || cpu == cpuid ) {
		if( !single_cpu ) {
			tidlemsk = idle_cpus_mask;
			CPU_NAND(&tidlemsk, &hlt_cpus_mask);
			CPU_CLR(cpuid, &tidlemsk);
		}

		if( (flags & SRQ_YIELDING) == 0 && maybe_preempt(td) )
			return;
		else
			usched_try_resched(td);
	}

	if( (td->td_flags & TDF_NOLOAD) == 0 )
		usched_load_cnt_inc();

	runq_add(ts->ts_runq, td, flags);

	if( cpu != NOCPU )
		runq_length[cpu]++;
}

/*
 * Remove thread from running queue
 */
void sched_rem(struct thread *td) {
	struct td_sched *ts;

	ts = td->td_sched;
	KASSERT(td->td_flags & TDF_INMEM, ("thread swapped out"));
	KASSERT(TD_ON_RUNQ(td), ("thread not on run queue"));
	mtx_assert(&sched_lock, MA_OWNED);

	if( (td->td_flags & TDF_NOLOAD) == 0 )
		usched_load_cnt_dec();
#ifdef SMP
	if( ts->ts_runq != &runq )
		runq_length[ts->ts_runq - runq_pcpu]--;
#endif
	runq_remove(ts->ts_runq, td);
	TD_SET_CAN_RUN(td);
}

void sched_clock(struct thread *td) {
	struct pcpuidlestat *stat;
	struct td_sched *ts;

	THREAD_LOCK_ASSERT(td, MA_OWNED);
	ts = td->td_sched;

	ts->ts_cpu_ticks++;
	td->td_estcpu = ESTCPULIM(td->td_estcpu + 1);
	if( (td->td_estcpu % INVERSE_ESTCPU_WEIGHT) == 0 ) {
		usched_reset_priority(td);
		usched_reset_priority_thread(td);
	}

	// Force a context switch if the current thread has used up a full
	// time slice (default is 100ms).
	if( !TD_IS_IDLETHREAD(td) && --ts->ts_slice <= 0) {
		ts->ts_slice = sched_slice;
		td->td_flags |= TDF_NEEDRESCHED | TDF_SLICEEND;
	}

	stat = DPCPU_PTR(idlestat);
	stat->oldidlecalls = stat->idlecalls;
	stat->idlecalls = 0;
}


/*
 * Called every hz tick
 */
void sched_tick(int cnt) {
}

/*
 * Yield
 */
void sched_relinquish(struct thread *td) {
	thread_lock(td);
	mi_switch(SW_VOL | SWT_RELINQUISH, NULL);
	thread_unlock(td);
}

/*
 * Select threads to run.
 */
struct thread *sched_choose(void) {
	struct thread *td;
	struct runq *rq;

	mtx_assert(&sched_lock,  MA_OWNED);
#ifdef SMP
	struct thread *tdcpu;

	rq = &runq;
	tdcpu = runq_choose(&runq_pcpu[PCPU_GET(cpuid)]);
	td = runq_choose(&runq);
	if(td == NULL || (tdcpu != NULL && tdcpu->td_priority < td->td_priority)){
		td = tdcpu;
		rq = &runq_pcpu[PCPU_GET(cpuid)];
	}

#else
	rq = &runq;
	td = runq_choose(&runq);
#endif

	if( td ) {
#ifdef SMP
		if( td == tdcpu )
			runq_length[PCPU_GET(cpuid)]--;
#endif
		runq_remove(rq, td);
		td->td_flags |= TDF_DIDRUN;

		KASSERT(td->td_flags & TDF_INMEM,("thread swapped out"));
		return (td);
	}
	return (PCPU_GET(idlethread));
}

/*
 * Scheduler idle process.
 */
void sched_idletd(void *dummy) {
	struct pcpuidlestat *stat;

	THREAD_NO_SLEEPING(); // Deny sleep for curthread
	stat = DPCPU_PTR(idlestat);
	for (;;) {
		mtx_assert(&Giant, MA_NOTOWNED);

		while (sched_runnable() == 0) {
			cpu_idle(stat->idlecalls + stat->oldidlecalls > 64);
			stat->idlecalls++;
		}

		mtx_lock_spin(&sched_lock);
		mi_switch(SW_VOL | SWT_IDLE, NULL);
		mtx_unlock_spin(&sched_lock);
	}
}

/*
 * Binding makes cpu affinity permanent while pinning is used to temporarily
 * hold a thread on a particular CPU.
 */

/*
 * Bind thread to given cpu
 */
void sched_bind(struct thread *td, int cpu) {
	struct td_sched *ts;

	THREAD_LOCK_ASSERT(td, MA_OWNED|MA_NOTRECURSED);

	ts = td->td_sched;

	td->td_flags |= TDF_BOUND;
#ifdef SMP
	ts->ts_runq = &runq_pcpu[cpu];
	if( PCPU_GET(cpuid) == cpu )
		return;

	mi_switch(SW_VOL, NULL);
#endif
}

/*
 * Release thread
 */
void sched_unbind(struct thread* td) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	td->td_flags &= ~TDF_BOUND;
}

/*
 * Check if thread is bound to cpu
 */
int sched_is_bound(struct thread *td) {
	THREAD_LOCK_ASSERT(td, MA_OWNED);
	return (td->td_flags & TDF_BOUND);
}

/*
 * Multiprocessor feature to balance threads between cpus
 * Not yet implemented
 */
void sched_affinity(struct thread *td){

}

/*
 * These procedures tell the process data structure allocation code how
 * many bytes to actually allocate.
 */

/*
 * Debug function to get proc size
 */
int sched_sizeof_proc(void) {
	return (sizeof(struct proc));
}

/*
 * Get total size of thread struct + scheduler info for thread
 */
int sched_sizeof_thread(void) {
	return (sizeof(struct thread) + sizeof(struct td_sched));
}

/*
 * This routine provides a consistent thread name for use with KTR graphing
 * functions.
 */

/*
 * Debug method, used to get name of running thread
 */
char *sched_tdname(struct thread *td) {
#ifdef KTR
	struct td_sched *ts;

	ts = td->td_sched;
	if( ts->ts_name[0] == '\0' )
		snprintf(ts->ts_name, sizeof(ts->ts_name),
			"%s tid %d", td->td_name, td->td_tid);
	return (ts->ts_name);
#else
	return (td->td_name);
#endif
}

#ifdef KTR
void sched_clear_tdname(struct thread *td) {
	struct td_sched *ts;

	ts = td->td_sched;
	ts->ts_name[0] = '\0';
}
#endif

/*
 * Fixup scheduler state for proc0 and thread0
 */
void schedinit(void) {
	/*
	 * Set up the scheduler specific parts of proc0.
	 */
	proc0.p_sched = NULL; /* XXX */
	thread0.td_sched = &td_sched0;
	thread0.td_lock = &sched_lock;
	td_sched0.ts_slice = sched_slice;
	mtx_init(&sched_lock, "sched lock", NULL, MTX_SPIN | MTX_RECURSE);
}

/*
 * Calculate kernel quantum
 */
static int sysctl_kern_quantum(SYSCTL_HANDLER_ARGS) {
	int error, new_val, period;

	period = 1000000 / realstathz;
	new_val = period * sched_slice;
	error = sysctl_handle_int(oidp, &new_val, 0, req);
	if( error != 0 || req->newptr == NULL )
		return (error);
	if( new_val <= 0 )
		return (EINVAL);
	sched_slice = imax(1, (new_val + period / 2) / period);
	hogticks = imax(1, (2 * hz * sched_slice + realstathz / 2) / realstathz);
	return (0);
}

/*
 * Scheduler sysctl node
 */
SYSCTL_NODE(_kern, OID_AUTO, sched, CTLFLAG_RD, 0, "Scheduler");

SYSCTL_STRING(_kern_sched, OID_AUTO, name, CTLFLAG_RD, "uSched", 0,
    "Scheduler name");
SYSCTL_PROC(_kern_sched, OID_AUTO, quantum, CTLTYPE_INT | CTLFLAG_RW,
    NULL, 0, sysctl_kern_quantum, "I",
    "Quantum for timeshare threads in microseconds");
SYSCTL_INT(_kern_sched, OID_AUTO, slice, CTLFLAG_RW, &sched_slice, 0,
    "Quantum for timeshare threads in stathz ticks");

SYSCTL_INT(_kern_sched, OID_AUTO, td_count, CTLFLAG_RW, &sched_td_count, 0,
    "Value of thread counter");


SDT_PROVIDER_DEFINE(sched);

SDT_PROBE_DEFINE3(sched, , , change__pri, "struct thread *",
    "struct proc *", "uint8_t");
SDT_PROBE_DEFINE3(sched, , , dequeue, "struct thread *",
    "struct proc *", "void *");
SDT_PROBE_DEFINE4(sched, , , enqueue, "struct thread *",
    "struct proc *", "void *", "int");
SDT_PROBE_DEFINE4(sched, , , lend__pri, "struct thread *",
    "struct proc *", "uint8_t", "struct thread *");
SDT_PROBE_DEFINE2(sched, , , load__change, "int", "int");
SDT_PROBE_DEFINE2(sched, , , off__cpu, "struct thread *",
    "struct proc *");
SDT_PROBE_DEFINE(sched, , , on__cpu);
SDT_PROBE_DEFINE(sched, , , remain__cpu);
SDT_PROBE_DEFINE2(sched, , , surrender, "struct thread *",
    "struct proc *");
