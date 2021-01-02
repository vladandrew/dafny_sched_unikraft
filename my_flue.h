void schedcoop_thread_woken(struct uk_sched *s, struct uk_thread *t);
void schedcoop_schedule(struct uk_sched *s);
int schedcoop_thread_add(struct uk_sched *s, struct uk_thread *t,
                const uk_thread_attr_t *attr __unused);
void schedcoop_thread_remove(struct uk_sched *s, struct uk_thread *t);
void schedcoop_yield(struct uk_sched *s);
void idle_thread_fn(void *unused __unused);
void schedcoop_thread_blocked(struct uk_sched *s, struct uk_thread *t);


