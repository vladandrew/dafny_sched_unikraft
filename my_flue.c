#include <uk/sched.h>
#include <uk/plat/lcpu.h>
#include <uk/schedcoop.h>
#include <uk/plat/memory.h>
#include <uk/plat/time.h>
#include "my_flue.h"

uint64_t uk_schedcoop_init(struct uk_alloc *a)
{
        struct schedcoop_private *prv = NULL;
        struct uk_sched *sched = NULL;

	init_sched_ctor();

        uk_pr_info("Initializing cooperative scheduler\n");

        sched = uk_sched_create(a, 0);
        if (sched == NULL)
                return NULL;

        ukplat_ctx_callbacks_init(&sched->plat_ctx_cbs, ukplat_ctx_sw);

        uk_sched_idle_init(sched, NULL, idle_thread_fn);

        uk_sched_init(sched,
                        schedcoop_yield,
                        schedcoop_thread_add,
                        schedcoop_thread_remove,
                        schedcoop_thread_blocked,
                        schedcoop_thread_woken,
                        NULL, NULL, NULL, NULL);
	uk_pr_info("WOLO%p\n", sched);
        return (uint64_t) sched;
}

