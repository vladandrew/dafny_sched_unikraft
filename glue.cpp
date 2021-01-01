#include <sched.h>

static void schedcoop_thread_woken(struct uk_sched *s, struct uk_thread *t)
{
}
                                                                                                                                                                                                                   
static void schedcoop_schedule(struct uk_sched *s)
{
}
 
static int schedcoop_thread_add(struct uk_sched *s, struct uk_thread *t,
|       |       const uk_thread_attr_t *attr __unused)
{
 
}
 
static void schedcoop_thread_remove(struct uk_sched *s, struct uk_thread *t)
{
}
 
static void schedcoop_yield(struct uk_sched *s) 
{
|       schedcoop_schedule(s);
}
 
struct uk_sched *uk_schedcoop_init(struct uk_alloc *a) 
{
}
 


