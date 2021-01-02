
#include "sched.h"

_module::SchedCoop sched_coop;
#ifdef __cplusplus
	extern "C" {
#endif

#include <uk/sched.h>
#include <uk/plat/lcpu.h>
#include <uk/schedcoop.h>
#include <uk/plat/memory.h>
#include <uk/plat/time.h>

void schedcoop_thread_woken(struct uk_sched *s, struct uk_thread *t)
{
}
                                                                                                                                                                                                                   
void schedcoop_schedule(struct uk_sched *s)
{
	struct uk_thread *prev, *next, *thread, *tmp;
	_module::Thread *t = sched_coop.schedule().get();
	next = (uk_thread *)t->uk_thread;
	
	prev = uk_thread_current();

	if (prev != next)
		uk_sched_thread_switch(s, prev, next);

}
 
int schedcoop_thread_add(struct uk_sched *s, struct uk_thread *t,
		const uk_thread_attr_t *attr __unused)
{
	unsigned long flags;
	flags = ukplat_lcpu_save_irqf();
	_module::Thread *thread = new _module::Thread();
	thread->uk_sched = (uint64)s;
	thread->uk_thread = (uint64)t;

	std::shared_ptr<_module::Thread> my_ptr(thread);
	sched_coop.thread__add(my_ptr);
	ukplat_lcpu_restore_irqf(flags);
	return 0;
}
 
void schedcoop_thread_remove(struct uk_sched *s, struct uk_thread *t)
{
		if (t == uk_thread_current()) {
			schedcoop_schedule(s);
			uk_pr_warn("schedule() returned! Trying again\n");
		}
}
 
void schedcoop_yield(struct uk_sched *s) 
{
	schedcoop_schedule(s);
}

void idle_thread_fn(void *unused __unused)
{
	struct uk_thread *current = uk_thread_current();
	struct uk_sched *s = current->sched;

	s->threads_started = true;
	ukplat_lcpu_enable_irq();

	while (1) {
		uk_thread_block(current);
		schedcoop_schedule(s);
	}
}


void schedcoop_thread_blocked(struct uk_sched *s, struct uk_thread *t)
{
	UK_ASSERT(ukplat_lcpu_irqs_disabled());
}

void init_sched_ctor()
{
	sched_coop.__ctor();
}
 
#ifdef __cplusplus
}
#endif

