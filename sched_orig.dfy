predicate unique(q : seq<Thread>)
{
    forall i :: 0 <= i < |q| ==> q[i] !in /*q[..i] +*/ q[i + 1..]
}

predicate included(small : seq<Thread>, large : seq<Thread>)
{
    forall thread | thread in small :: thread in large
}

predicate included_set(small : seq<Thread>, large : seq<Thread>)
{
    setify(small) <= setify(large)
}

predicate disjoint(a : seq<Thread>, b : seq<Thread>)
{
    forall thread :: thread in a ==> thread !in b
    &&
    forall thread :: thread in b ==> thread !in a
}

predicate disjoint_set(a : seq<Thread>, b : seq<Thread>)
{
    setify(a) !! setify(b)
}

predicate prefix_from(a : seq<Thread>, b : seq<Thread>, i : nat)
{
    i <= |b| && a == b[..i]
}

predicate prefix(a : seq<Thread>, b : seq<Thread>)
{
    a <= b
}

predicate suffix_from(a : seq<Thread>, b : seq<Thread>, i : nat)
{
    i <= |b| && a == b[i..]
}

predicate suffix(a : seq<Thread>, b : seq<Thread>)
{
    a == []
    ||
    (|a| <= |b| && a == b[|b| - |a|..])
}

function setify(a : seq<Thread>) : set<Thread>
{
    set t | t in a
}

lemma ordered_set(a : seq<Thread>)
    requires unique(a)
    ensures forall t :: t in a ==> t in setify(a)
    ensures forall t :: t in setify(a) ==> t in a
{
}
 
lemma incl_set(a : seq<Thread>, b : seq<Thread>)
    requires included_set(a, b)
    requires unique(a)
    requires unique(b)
    ensures included(a, b)
{
    ordered_set(a);
    ordered_set(b);
}

lemma diff(a : seq<Thread>, b : seq<Thread>, c : seq<Thread>)
    requires included(a, c)
    requires unique(b)
    requires unique(c)
    requires setify(a) + setify(b) == setify(c)
    ensures included(b, c)
{
    incl_set(b, c);
}

lemma sorted_concat(left : seq<Thread>, right : seq<Thread>)
    requires forall t | t in left :: t.wakeup_time == 0
    requires sorted(right)
    ensures sorted(left + right)
{

}

lemma unique_seq(a : seq<Thread>)
    requires unique(a)
    ensures |a| == |setify(a)|
{
    var ss : set<Thread> := {};
    var i := 0;

    while i < |a|
        invariant i <= |a|
        invariant ss == setify(a[..i])
        invariant |a[..i]| == |setify(a[..i])|
    {
        ss := ss + {a[i]};
        i := i + 1;
    }

    assert |a[..i]| == |setify(a[..i])|;
    assert a[..i] == a;
    assert |a| == |setify(a)|;
}

lemma subset_of_void(small : seq<Thread>, large : seq<Thread>)
    requires unique(small)
    requires unique(large)
    requires included(small, large)
    ensures large == [] ==> small == []
{
    unique_seq(small);
}

predicate ordered_projection(small : seq<Thread>, large : seq<Thread>)
{
    forall i, j :: 0 <= i < j < |large| && large[i] in small && large[j] in small 
                            ==> (exists k, l :: 0 <= k < l < |small| && small[k] == large[i] && small[l] == large[j])
}

predicate sorted(a : seq<Thread>)
reads a
{
    forall i, j | 0 <= i < j < |a| :: a[i].wakeup_time <= a[j].wakeup_time
}

lemma zero_start(left : seq<Thread>, right : seq<Thread>, whole : seq<Thread>)
    requires forall t : Thread | t in left :: t.wakeup_time == 0
    requires sorted(right)
    requires whole == left + right
    ensures sorted(whole)
{

}

function partition_point(a : seq<Thread>, wkt : nat) : nat
    reads a
    requires sorted(a)
    ensures 0 <= partition_point(a, wkt) <= |a|
    ensures forall i | 0 <= i < partition_point(a, wkt) :: a[i].wakeup_time <= wkt
    ensures forall i | partition_point(a, wkt) <= i < |a| :: a[i].wakeup_time > wkt
{
    if a == [] || a[0].wakeup_time > wkt
    then 0
    else 1 + partition_point(a[1..], wkt)
}

class Thread {
    var name        : string;
    var stack       : nat;
    var ctx         : nat;
    var runnable    : bool;
    var queueable   : bool;
    var exited      : bool;
    var flags       : bv16;
    var wakeup_time : nat;
    var detached    : bool;
    var sched       : SchedCoop?;

    constructor(n : string, s: SchedCoop)
    ensures is_runnable()
    ensures !is_queueable()
    ensures !is_exited()
    ensures wakeup_time == 0
    ensures name == n
    ensures sched == s
    ensures fresh(this)
    {
        runnable    := true;
        queueable   := false;
        exited      := false;
        flags       := 0;
        stack       := 1;
        name        := n;
        wakeup_time := 0;
        detached    := false;
        sched       := s;
    }

    constructor NoName(s: SchedCoop)
    ensures is_runnable()
    ensures !is_queueable()
    ensures !is_exited()
    ensures wakeup_time == 0
    ensures name == "" 
    ensures sched == s
    ensures fresh(this)
    {
        runnable    := true;
        queueable   := false;
        exited      := false;
        flags       := 0;
        stack       := 1;
        name        := "";
        wakeup_time := 0;
        detached    := false;
        sched       := s;
    }

    constructor NoSched(n : string)
    ensures is_runnable()
    ensures !is_queueable()
    ensures !is_exited()
    ensures wakeup_time == 0
    ensures name == n
    ensures fresh(this)
    {
        runnable    := true;
        queueable   := false;
        exited      := false;
        flags       := 0;
        stack       := 1;
        name        := n;
        wakeup_time := 0;
        detached    := false;
    }

    method setScheduler(s : SchedCoop)
    modifies this
    ensures sched == s
    {
        sched := s;
    }

    function method is_runnable() : bool
    reads this
    {
        runnable
    }

    method set_runnable()
    modifies this
    ensures exited == old(exited)
    ensures queueable == old(queueable)
    ensures is_runnable()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        runnable := true;
    }

    method clear_runnable()
    modifies this
    ensures exited == old(exited)
    ensures queueable == old(queueable)
    ensures !is_runnable()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        runnable := false;
    }

    function method is_exited() : bool
    reads this
    {
        exited
    }

    method set_exited()
    modifies this
    ensures queueable == old(queueable)
    ensures runnable == old(runnable)
    ensures is_exited()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        exited := true;
    }

    method clear_exited()
    modifies this
    ensures queueable == old(queueable)
    ensures runnable == old(runnable)
    ensures !is_exited()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        exited := false;
    }

    function method is_queueable() : bool
    reads this
    {
        queueable
    }

    method set_queueable()
    modifies this
    ensures exited == old(exited)
    ensures runnable == old(runnable)
    ensures is_queueable()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        queueable := true;
    }

    method clear_queueable()
    modifies this
    ensures exited == old(exited)
    ensures runnable == old(runnable)
    ensures !is_queueable()
    ensures this == old(this)
    ensures wakeup_time == old(wakeup_time)
    ensures sched == old(sched)
    {
        queueable := false;
    }

    method set_wakeup_time(delta : nat)
    modifies this
    ensures wakeup_time == delta
    {
        wakeup_time := delta;
    }
}

class ExitedQueue {
    var q : seq<Thread>

    constructor()
    ensures Valid()
    ensures q == []
    ensures fresh(this)
    {
        q := [];
    }

    constructor Init(queue : seq<Thread>)
    requires forall i :: 0 <= i < |queue| ==> (elemValid(queue[i]) && queue[i] !in (queue[..i] + queue[i + 1..]))
    ensures Valid()
    ensures q == queue
    ensures fresh(this)
    {
        q := queue;
    }

    static predicate elemValid(t : Thread)
    reads t
    {
        t.is_exited()
    }

    predicate Valid()
    reads this, q
    {
        forall i :: 0 <= i < |q| ==> (elemValid(q[i]) && q[i] !in (q[..i] + q[i + 1..]))
    }

    function method Length() : nat
    reads this, q
    {
        |q|
    }

    function method isEmpty() : bool
    reads this, q
    {
        |q| == 0
    }

    function method get_at(i : nat) : Thread
    reads this, q
    requires 0 <= i < Length()
    {
        q[i]
    }

    method pushback(t : Thread)
    modifies this
    requires Valid()
    requires elemValid(t) && t !in q
    ensures q == old(q) + [t]
    ensures Valid()
    ensures this == old(this)
    ensures prefix(old(q), q)
    {
        q := q + [t];
    }

    function method peek() : Thread
    reads this, q
    requires Valid()
    requires |q| > 0
    ensures Valid()
    {
        q[0]
    }

    method pop() returns (t : Thread)
    modifies this
    requires Valid()
    requires !isEmpty()
    ensures [t] + q == old(q)
    ensures t == old(q)[0]
    ensures t in old(q)
    ensures q == old(q)[1..]
    ensures |q| == |old(q)| - 1
    ensures elemValid(t)
    ensures Valid()
    ensures t.wakeup_time == old(t.wakeup_time)
    ensures forall t :: t in q ==> t.wakeup_time == old(t.wakeup_time)
    ensures this == old(this)
    {
        t := q[0];
        q := q[1..];
    }

    method get_index(t : Thread) returns (i : nat)
    ensures if i < Length() then t == q[i] else t !in q
    {
        i := 0;

        while (i < Length())
        invariant 0 <= i <= Length()
        invariant t !in q[..i]
        {
            if (q[i] == t)
            {
                break;
            }

            i := i + 1;
        }
    }

    method remove(t : Thread)
    modifies this
    requires Valid()
    ensures Valid()
    ensures this == old(this)
    ensures t in old(q) ==> t !in q
    ensures forall x :: x !in old(q) ==> x !in q
    {
        var i := get_index(t);

        if (i < Length())
        {
            q := q[..i] + q[i + 1..];
        }
    }

    method remove_at(i : nat)
    modifies this
    requires Valid()
    requires 0 <= i < |q|
    ensures |q| == |old(q)| - 1
    ensures Valid()
    ensures this == old(this)
    {
        q := q[..i] + q[i + 1..];
    }
}

class RunnableQueue {
    var q : seq<Thread>

    constructor()
    ensures Valid()
    ensures q == []
    ensures fresh(this)
    {
        q := [];
    }

    constructor Init(queue : seq<Thread>)
    requires forall i :: 0 <= i < |queue| ==> (elemValid(queue[i]) && queue[i] !in (queue[..i] + queue[i + 1..]))
    ensures Valid()
    ensures q == queue
    ensures fresh(this)
    {
        q := queue;
    }

    static predicate elemValid(t : Thread)
    reads t
    {
        t.is_runnable()
        &&
        t.wakeup_time == 0
    }

    predicate Valid()
    reads this, q
    {
        forall i :: 0 <= i < |q| ==> (elemValid(q[i]) && q[i] !in (q[..i] + q[i + 1..]))
    }

    function method Length() : nat
    reads this, q
    {
        |q|
    }

    function method isEmpty() : bool
    reads this, q
    {
        |q| == 0
    }

    function method get_at(i : nat) : Thread
    reads this, q
    requires 0 <= i < Length()
    ensures Length() > 0
    {
        q[i]
    }

    method pushback(t : Thread)
    modifies this
    requires Valid()
    requires elemValid(t) && t !in q
    ensures |q| > 0
    ensures q == old(q) + [t]
    ensures Valid()
    ensures this == old(this)
    ensures prefix(old(q), q)
    {
        q := q + [t];
    }

    function method peek() : Thread
    reads this, q
    requires Valid()
    requires |q| > 0
    ensures |q| > 0
    ensures Valid()
    {
        q[0]
    }

    method pop() returns (t : Thread)
    modifies this
    requires Valid()
    requires !isEmpty()
    ensures [t] + q == old(q)
    ensures t == old(q)[0]
    ensures t in old(q)
    ensures q == old(q)[1..]
    ensures |q| == |old(q)| - 1
    ensures elemValid(t)
    ensures Valid()
    ensures t.wakeup_time == old(t.wakeup_time)
    ensures forall t :: t in q ==> t.wakeup_time == old(t.wakeup_time)
    ensures this == old(this)
    {
        t := q[0];
        q := q[1..];
    }

    method get_index(t : Thread) returns (i : nat)
    ensures if i < Length() then t == q[i] else t !in q
    {
        i := 0;

        while (i < Length())
        invariant 0 <= i <= Length()
        invariant t !in q[..i]
        {
            if (q[i] == t)
            {
                break;
            }

            i := i + 1;
        }
    }

    method remove(t : Thread)
    modifies this
    requires Valid()
    ensures Valid()
    ensures this == old(this)
    ensures t in old(q) ==> t !in q
    ensures forall x :: x !in old(q) ==> x !in q
    {
        var i := get_index(t);

        if (i < Length())
        {
            q := q[..i] + q[i + 1..];
        }
    }

    method remove_at(i : nat)
    modifies this
    requires Valid()
    requires 0 <= i < |q|
    ensures |q| == |old(q)| - 1
    ensures Valid()
    ensures this == old(this)
    {
        q := q[..i] + q[i + 1..];
    }
}

class SleepingQueue {
    var q : seq<Thread>

    constructor()
    ensures Valid()
    ensures q == []
    ensures fresh(this)
    {
        q := [];
    }

    constructor Init(queue : seq<Thread>)
    requires forall i :: 0 <= i < |queue| ==> (elemValid(queue[i]) && queue[i] !in (queue[..i] + queue[i + 1..]))
    requires sorted(queue)
    ensures Valid()
    ensures q == queue
    ensures fresh(this)
    {
        q := queue;
    }

    static predicate elemValid(t : Thread)
    reads t
    {
        !t.is_runnable()
    }

    predicate Valid()
    reads this, q
    {
        forall i | 0 <= i < |q| :: elemValid(q[i])
        &&
        unique(q)
        &&
        sorted(q)
    }

    function method Length() : nat
    reads this, q
    {
        |q|
    }

    function method isEmpty() : bool
    reads this, q
    {
        |q| == 0
    }

    function method get_at(i : nat) : Thread
    reads this, q
    requires 0 <= i < Length()
    ensures Length() > 0
    {
        q[i]
    }

    function method peek() : Thread
    reads this, q
    requires Valid()
    requires |q| > 0
    ensures |q| > 0
    ensures Valid()
    {
        q[0]
    }

    method pop() returns (t : Thread)
    modifies this
    requires Valid()
    requires !isEmpty()
    ensures [t] + q == old(q)
    ensures t == old(q)[0]
    ensures t in old(q)
    ensures q == old(q)[1..]
    ensures |q| == |old(q)| - 1
    ensures elemValid(t)
    ensures Valid()
    ensures t.wakeup_time == old(t.wakeup_time)
    ensures forall t :: t in q ==> t.wakeup_time == old(t.wakeup_time)
    ensures this == old(this)
    {
        t := q[0];
        q := q[1..];
    }

    method get_index(t : Thread) returns (i : nat)
    ensures if i < Length() then t == q[i] else t !in q
    {
        i := 0;

        while (i < Length())
        invariant 0 <= i <= Length()
        invariant t !in q[..i]
        {
            if (q[i] == t)
            {
                break;
            }

            i := i + 1;
        }
    }

    method remove(t : Thread)
    modifies this
    requires Valid()
    ensures Valid()
    ensures this == old(this)
    ensures t in old(q) ==> t !in q
    ensures forall x :: x !in old(q) ==> x !in q
    {
        var i := get_index(t);

        if (i < Length())
        {
            q := q[..i] + q[i + 1..];
        }
    }
 
    method remove_at(i : nat)
    modifies this
    requires Valid()
    requires 0 <= i < |q|
    ensures |q| == |old(q)| - 1
    ensures Valid()
    ensures this == old(this)
    {
        q := q[..i] + q[i + 1..];
    }

    method bin_src(wkt : nat) returns (ind : int)
        requires sorted(q)
        ensures ind >= 0 ==> ind < |q| && q[ind].wakeup_time == wkt
        ensures ind < 0 ==> forall i | 0 <= i < |q| :: q[i].wakeup_time != wkt
    {
        var l, r := 0, |q|;

        while l < r
            invariant 0 <= l <= r <= |q|
            invariant forall i | 0 <= i < l :: q[i].wakeup_time < wkt
            invariant forall i | r <= i < |q| :: q[i].wakeup_time > wkt
        {
            var m := (l + r) / 2;

            if wkt < q[m].wakeup_time
            {
                r := m;
            }
            else if wkt > q[m].wakeup_time
            {
                l := m + 1;
            }
            else
            {
                return m;
            }
        }

        return -1;
    }

    method find_insert_point(wkt : nat) returns (ind : nat)
        requires Valid()
        ensures Valid()
        ensures 0 <= ind <= |q|
        ensures forall t : Thread | t in q[..ind] :: t.wakeup_time <= wkt
        ensures forall t : Thread | t in q[ind..] :: t.wakeup_time > wkt
        ensures ind == partition_point(q, wkt)
    {
        var l, r := 0, |q|;

        while l < r
            invariant 0 <= l <= r <= |q|
            invariant forall t : Thread | t in q[..l] :: t.wakeup_time <= wkt
            invariant forall t : Thread | t in q[r..] :: t.wakeup_time > wkt
            invariant l <= partition_point(q, wkt) <= r
        {
            var m := (l + r) / 2;

            if q[m].wakeup_time > wkt
            {
                r := m;
            }
            else
            {
                l := m + 1;
            }
        }

        assert l == r;

        ind := l;
    }

    method insert(t : Thread)
        modifies this
        requires t !in q
        requires elemValid(t)
        requires Valid()
        ensures Valid()
        ensures q == old(q[..partition_point(q, t.wakeup_time)]) + [t] + old(q[partition_point(q, t.wakeup_time)..])

        ensures t in q
        ensures q[partition_point(old(q), t.wakeup_time)] == t

        ensures this == old(this)
    {
        var ind := find_insert_point(t.wakeup_time);

        q := q[..ind] + [t] + q[ind..];
    }

    method partition(wkt : nat) returns (smaller : seq<Thread>)
        modifies this
        requires Valid()
        ensures Valid()
        ensures unique(smaller) && sorted(smaller)
        ensures forall t | t in smaller :: elemValid(t)
        ensures smaller == old(q[..partition_point(q, wkt)])
        ensures forall t : Thread | t in smaller :: t.wakeup_time <= wkt
        ensures q == old(q[partition_point(q, wkt)..])
        ensures forall t : Thread | t in q :: t.wakeup_time > wkt
        ensures |smaller| == partition_point(old(q), wkt)

        ensures this == old(this)
    {
        var ind := find_insert_point(wkt);

        smaller := q[..ind];
        q := q[ind..];
    }
}


class SchedCoop {
    var current          : Thread;
    var crt_clock        : nat;
    var thread_list      : RunnableQueue;
    var sleeping_threads : SleepingQueue;
    var exited_threads   : ExitedQueue;
    var idle             : Thread;
    var threads_started  : bool;
    ghost var all : set<Thread>;

    constructor()
    ensures sched_inv()
    ensures fresh(this)
    ensures thread_list.isEmpty()
    ensures sleeping_threads.isEmpty()
    ensures exited_threads.isEmpty()
    ensures fresh(thread_list)
    ensures fresh(sleeping_threads)
    ensures fresh(exited_threads)
    ensures fresh(idle)
    ensures current == idle
    ensures all == {}
    ensures all == get_all_threads()
    ensures crt_clock == 0
    {
        crt_clock := 0;

        thread_list      := new RunnableQueue();
        sleeping_threads := new SleepingQueue();
        exited_threads   := new ExitedQueue();

        threads_started  := false;

        idle             := new Thread.NoSched("Idle");

        current          := idle;

        all := {};
    }

    function get_all_threads() : set<Thread>
    reads this, thread_list, sleeping_threads
    {
        setify(thread_list.q) + setify(sleeping_threads.q) + {current} - {idle}
    }

    function method get_all_threads_seq() : seq<Thread>
    reads this, thread_list, sleeping_threads
    {
        thread_list.q + sleeping_threads.q + (if current != idle then [current] else [])
    }

    method init()
    modifies idle
    {
        idle.setScheduler(this);
    }

    method thread_add(t : Thread)
    modifies this, t, thread_list
    requires t !in thread_list.q
    requires t !in sleeping_threads.q
    requires t != current
    requires t != idle
    requires sched_inv()
    ensures sched_inv()
    ensures thread_list == old(thread_list)
    ensures thread_list.q == old(thread_list.q) + [t]

    ensures this == old(this)
    ensures current == old(current)
    ensures idle == old(idle)
    ensures sleeping_threads == old(sleeping_threads)
    ensures exited_threads == old(exited_threads)
    ensures crt_clock == old(crt_clock)

    ensures all == old(all) + {t}
    requires all == get_all_threads()
    ensures all == get_all_threads()
    {
        t.set_runnable();
        t.wakeup_time := 0;
        thread_list.pushback(t);
        all := all + {t};
    }

    predicate sched_inv()
    reads this, thread_list, thread_list.q[..], sleeping_threads, sleeping_threads.q[..], current, all, idle
    {
        thread_list.Valid()
        &&
        sleeping_threads.Valid()
        &&
        current !in thread_list.q
        &&
        current !in sleeping_threads.q
        &&
        idle !in thread_list.q
        &&
        idle !in sleeping_threads.q
        &&
        thread_list.elemValid(current)
        &&
        thread_list.elemValid(idle)
        &&
        forall t | t in sleeping_threads.q :: t.wakeup_time > crt_clock
    }

    method update_sleeping()
        modifies this, thread_list, sleeping_threads, sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]
        requires sched_inv()
        ensures sched_inv()

        ensures crt_clock == old(crt_clock) + 1
        ensures thread_list.q == old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)])
        ensures sleeping_threads.q == old(sleeping_threads.q[partition_point(sleeping_threads.q, crt_clock + 1)..])

        requires all == get_all_threads()
        ensures all == get_all_threads()
        ensures all == old(all)

        ensures this == old(this)
        ensures thread_list == old(thread_list)
        ensures sleeping_threads == old(sleeping_threads)
        ensures idle == old(idle)
        ensures current == old(current)
    {
        crt_clock := crt_clock + 1;

        var to_wake_up : seq<Thread> := sleeping_threads.partition(crt_clock);
        var i := 0;

        while i < |to_wake_up| 
            modifies thread_list, to_wake_up
            invariant 0 <= i <= |to_wake_up|
            invariant sched_inv()
            invariant thread_list.q == old(thread_list.q) + to_wake_up[..i]
            invariant forall t : Thread | t in to_wake_up[..i] :: t.wakeup_time == 0
        {
            var x := to_wake_up[i];

            x.wakeup_time := 0;
            x.set_runnable();

            assert x.is_runnable();
            thread_list.pushback(x);

            i := i + 1;
        }
    }

    method choose_next() returns (next : Thread)
        modifies this, thread_list
        requires sched_inv()
        ensures sched_inv()
        ensures this == old(this)
        ensures idle == old(idle)
        ensures crt_clock == old(crt_clock)
        ensures thread_list == old(thread_list)
        ensures sleeping_threads == old(sleeping_threads)
        ensures sleeping_threads.q == old(sleeping_threads.q)

        ensures old(thread_list.q) != [] ==> next == old(thread_list.q)[0]
        ensures old(thread_list.q) != [] ==> if old(current.is_runnable()) && old(current) != idle
                                                then thread_list.q == old(thread_list.q)[1..] + [old(current)]
                                                else thread_list.q == old(thread_list.q)[1..]
        ensures old(thread_list.q) == [] ==> if old(current.is_runnable())
                                                then next == old(current)
                                                else next == idle
        ensures old(thread_list.q) == [] ==> thread_list.q == []
        ensures current == next

        requires all == get_all_threads()
        ensures all == get_all_threads()
        ensures all == old(all)
    {
        var prev := current;

        if !thread_list.isEmpty()
        {
            next := thread_list.pop();

            if (prev != idle)
            {
                if (prev.is_runnable())
                {
                    thread_list.pushback(prev);
                }
            }
        }
        else if prev.is_runnable()
        {
            next := prev;
        }
        else
        {
            next := idle;
        }

        current := next;
    }

    method schedule() returns (next : Thread)
        modifies this, thread_list, sleeping_threads, sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]
        requires sched_inv()
        ensures sched_inv()
        ensures crt_clock == old(crt_clock) + 1

        ensures sleeping_threads.q == old(sleeping_threads.q[partition_point(sleeping_threads.q, crt_clock + 1)..])

        ensures if old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]) != []
                then next == (old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]))[0]
                else
                    if old(current.is_runnable())
                    then next == old(current)
                    else next == idle
        ensures if old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]) != []
                then
                    if old(current.is_runnable()) && old(current) != idle
                    then thread_list.q == (old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]))[1..] + [old(current)]
                    else thread_list.q == (old(thread_list.q) + old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + 1)]))[1..]
                else thread_list.q == []

        ensures next == current

        ensures thread_list == old(thread_list)
        ensures sleeping_threads == old(sleeping_threads)
        ensures this == old(this)
        ensures idle == old(idle)

        requires all == get_all_threads()
        ensures all == get_all_threads()
        ensures all == old(all)
    {
        update_sleeping();

        next := choose_next();
    }

    method current_sleep(how_long : nat) returns (next : Thread)
        modifies this, current, sleeping_threads
        requires how_long > 0
        requires current != idle
        requires sched_inv()
        ensures sched_inv()
        ensures old(current).wakeup_time == crt_clock + how_long + 1
        ensures sleeping_threads.q == old(sleeping_threads.q[..partition_point(sleeping_threads.q, crt_clock + how_long + 1)])
                                    + [old(current)]
                                    + old(sleeping_threads.q[partition_point(sleeping_threads.q, crt_clock + how_long + 1)..])
        ensures current == idle
        ensures next == current
        ensures old(current).sched == old(current.sched)

        ensures this == old(this)
        ensures sleeping_threads == old(sleeping_threads)
        ensures exited_threads == old(exited_threads)
        ensures thread_list.q == old(thread_list.q);
        ensures thread_list == old(thread_list)
        ensures idle == old(idle)
        ensures crt_clock == old(crt_clock)

        requires all == get_all_threads()
        ensures all == get_all_threads()
        ensures all == old(all)
    {
        current.wakeup_time := crt_clock + how_long + 1;
        current.runnable := false;
        sleeping_threads.insert(current);

        next := idle;
        current := next;
    }

    method thread_woken(t : Thread)
    modifies thread_list, sleeping_threads, t
    requires thread_list.Valid()
    requires sleeping_threads.Valid()
    ensures thread_list.Valid()
    ensures sleeping_threads.Valid()
    {
        if (t.is_runnable())
        {
            return;
        }

        if (t in sleeping_threads.q)
        {
            sleeping_threads.remove(t);
        }

        t.wakeup_time := 0;
        t.set_runnable();

        if (t != current || t.is_queueable())
        {
            thread_list.pushback(t);
            t.clear_queueable();
        }
    }
}

/* Proofs */

/*
method runnable_thread_will_run_complete(s : SchedCoop, target : Thread, should_sleep : seq<bool>, time_to_sleep : seq<nat>, should_add_thread : seq<bool>)
        modifies s, s.thread_list, s.sleeping_threads, s.all

        requires s.all == s.get_all_threads()
        requires s.sched_inv()
        requires |should_sleep| == |time_to_sleep| == |s.thread_list.q| == |should_add_thread|

        requires forall ts | ts in time_to_sleep :: ts > 0

        requires forall i :: 0 <= i < |time_to_sleep| ==> time_to_sleep[i] > 0

        requires target in s.thread_list.q
 
        ensures s.current == target
    {
        var i := 0;
        var crt := s.current;
        var target_pos := s.thread_list.get_index(target);
        var old_runnable_q := s.thread_list.q;
        var nr := target_pos + 1;
        var new_threads := {};

        while i < nr
            modifies s, s.thread_list, s.sleeping_threads, s.all

            invariant i <= nr <= |old_runnable_q|
            invariant s.sched_inv()
            invariant s.all == s.get_all_threads()
            invariant s.all == old(s.all) + new_threads
            invariant forall t | t in s.all :: if t in new_threads then fresh(t) else t in old(s.all)

            invariant prefix(old_runnable_q[i..], s.thread_list.q)
            invariant s.current != s.idle ==> s.current in old(s.all)
            invariant forall t | t in s.sleeping_threads.q :: t in old(s.all)
            invariant i < |old_runnable_q| ==> s.thread_list.q[0] == old_runnable_q[i];

            invariant i > 0 ==> s.current == old_runnable_q[i - 1]

            invariant s.idle == old(s.idle)
            invariant s == old(s)
            invariant s.sleeping_threads == old(s.sleeping_threads)
            invariant s.thread_list == old(s.thread_list)
        {
            assert s.thread_list.q[0] == old_runnable_q[i];

            if should_add_thread[i]
            {
                var t := new Thread.NoName(s);
                new_threads := new_threads + {t};

                t.set_runnable();
                t.wakeup_time := 0;
                s.thread_list.q := s.thread_list.q + [t];
                s.all := s.all + {t};
            }

            assert s.current != s.idle ==> s.current in s.all;

            if s.current != s.idle && should_sleep[i]
            {
                assert s.current in old(s.all);
                crt := s.current_sleep(time_to_sleep[i]);
            }
            assert new_threads <= s.all;

            crt := s.schedule();

            assert crt == old_runnable_q[i];

            i := i + 1;

            assert prefix(old_runnable_q[i..], s.thread_list.q);
        }
    }

    method runnable_thread_will_run(s : SchedCoop, target : Thread)
        modifies s, s.thread_list, s.sleeping_threads, s.sleeping_threads.q

        requires s.all == s.get_all_threads()
        requires s.sched_inv()

        requires target in s.thread_list.q
 
        ensures s.current == target
    {
        var i := 0;
        var crt := s.current;
        var target_pos := s.thread_list.get_index(target);
        var old_runnable_q := s.thread_list.q;
        var nr := target_pos + 1;

        while i < nr
            modifies s, s.thread_list, s.sleeping_threads, s.sleeping_threads.q

            invariant i <= nr <= |old_runnable_q|
            invariant s.sched_inv()
            invariant prefix(old_runnable_q[i..], s.thread_list.q)
            invariant i < |old_runnable_q| ==> s.thread_list.q[0] == old_runnable_q[i];
            invariant i > 0 ==> s.current == old_runnable_q[i - 1]

            invariant s.all == s.get_all_threads()

            invariant s == old(s)
            invariant s.sleeping_threads == old(s.sleeping_threads)
            invariant s.thread_list == old(s.thread_list)
            invariant suffix(s.sleeping_threads.q, old(s.sleeping_threads.q))
        {
            assert s.thread_list.q[0] == old_runnable_q[i];

            crt := s.schedule();

            assert crt == old_runnable_q[i];

            i := i + 1;
        }
    }

    method new_thread_will_run(s : SchedCoop, new_thread : Thread)
        modifies new_thread, s, s.thread_list, s.sleeping_threads, s.sleeping_threads.q

        requires s.all == s.get_all_threads()
        requires s.sched_inv()
        requires s.current != s.idle
 
        requires new_thread !in s.thread_list.q
        requires new_thread !in s.sleeping_threads.q
        requires new_thread !in s.exited_threads.q
        requires s.thread_list.elemValid(new_thread)
        requires new_thread != s.current
        requires new_thread != s.idle

        ensures s.current == new_thread
    {
        s.thread_add(new_thread);

        runnable_thread_will_run(s, new_thread);
    }

    method sleeping_thread_will_run(s : SchedCoop, target : Thread)
        modifies s, s.thread_list, s.sleeping_threads, s.all
        modifies s, s.thread_list, s.sleeping_threads, s.sleeping_threads.q, s.current

        requires s.all == s.get_all_threads()
        requires s.sched_inv()

        requires target in s.sleeping_threads.q

        ensures s.current == target
    {
        var crt : Thread;
        var current_time := s.crt_clock;
        var wakeup_time := target.wakeup_time;

        while current_time < wakeup_time
            modifies s, s.thread_list, s.sleeping_threads, s.sleeping_threads.q

            invariant s == old(s)
            invariant s.idle == old(s.idle)
            invariant s.sleeping_threads == old(s.sleeping_threads)
            invariant s.thread_list == old(s.thread_list)
            invariant target == old(target)

            invariant target in s.all

            invariant s.sched_inv()
            invariant s.all == s.get_all_threads()
            invariant s.all == old(s.all)
            invariant suffix(s.sleeping_threads.q, old(s.sleeping_threads.q))
            invariant s.crt_clock == current_time
            invariant forall t | t in s.sleeping_threads.q :: t.wakeup_time == old(t.wakeup_time)
            invariant forall t | t in old(s.sleeping_threads.q) :: old(t.wakeup_time) <= current_time ==> t !in s.sleeping_threads.q

        {
            assert target in s.all;
            crt := s.schedule();
            current_time := current_time + 1;
        }

        assert target in setify(s.thread_list.q) + setify(s.sleeping_threads.q) + {s.current} + {s.idle};
        assert target !in s.sleeping_threads.q;
        assert target in setify(s.thread_list.q) + {s.current};
        assert target in s.thread_list.q + [s.current];

        if target == s.current
        {
            return;
        }
        else
        {
            assert target in s.thread_list.q;
            runnable_thread_will_run(s, target);
        }
    }
 */
