// Dafny program sched.dfy compiled into Cpp
#include "DafnyRuntime.h"
#include "sched.h"
namespace _System  {










}// end of namespace _System 
namespace _module  {

  typedef uint64 uint64;

  void Thread::__ctor(DafnySequence<char> n, std::shared_ptr<_module::SchedCoop> s)
  {
    (this)->runnable = true;
    (this)->queueable = false;
    (this)->exited = false;
    (this)->flags = (uint16)0;
    (this)->stack = (uint64)1;
    (this)->name = n;
    (this)->wakeup__time = (uint64)0;
    (this)->detached = false;
    (this)->sched = s;
  }
  void Thread::NoName(std::shared_ptr<_module::SchedCoop> s)
  {
    (this)->runnable = true;
    (this)->queueable = false;
    (this)->exited = false;
    (this)->flags = (uint16)0;
    (this)->stack = (uint64)1;
    (this)->name = DafnySequenceFromString("");
    (this)->wakeup__time = (uint64)0;
    (this)->detached = false;
    (this)->sched = s;
  }
  void Thread::NoSched(DafnySequence<char> n)
  {
    (this)->runnable = true;
    (this)->queueable = false;
    (this)->exited = false;
    (this)->flags = (uint16)0;
    (this)->stack = (uint64)1;
    (this)->name = n;
    (this)->wakeup__time = (uint64)0;
    (this)->detached = false;
  }
  void Thread::setScheduler(std::shared_ptr<_module::SchedCoop> s)
  {
    (this)->sched = s;
  }
  bool Thread::is__runnable()
  {
    return this->runnable;
  }
  void Thread::set__runnable()
  {
    (this)->runnable = true;
  }
  void Thread::clear__runnable()
  {
    (this)->runnable = false;
  }
  bool Thread::is__exited()
  {
    return this->exited;
  }
  void Thread::set__exited()
  {
    (this)->exited = true;
  }
  void Thread::clear__exited()
  {
    (this)->exited = false;
  }
  bool Thread::is__queueable()
  {
    return this->queueable;
  }
  void Thread::set__queueable()
  {
    (this)->queueable = true;
  }
  void Thread::clear__queueable()
  {
    (this)->queueable = false;
  }
  void Thread::set__wakeup__time(uint64 delta)
  {
    (this)->wakeup__time = delta;
  }

  void ExitedQueue::__ctor()
  {
    (this)->q = DafnySequence<std::shared_ptr<_module::Thread>>::Create({});
  }
  void ExitedQueue::Init(DafnySequence<std::shared_ptr<_module::Thread>> queue)
  {
    (this)->q = queue;
  }
  uint64 ExitedQueue::Length()
  {
    return (uint64)((this->q).size());
  }
  bool ExitedQueue::isEmpty()
  {
    return ((this->q).size()) == (0);
  }
  std::shared_ptr<_module::Thread> ExitedQueue::get__at(uint64 i)
  {
    return (this->q).select(i);
  }
  void ExitedQueue::pushback(std::shared_ptr<_module::Thread> t)
  {
    (this)->q = (this->q).concatenate((DafnySequence<std::shared_ptr<_module::Thread>>::Create({t})));
  }
  std::shared_ptr<_module::Thread> ExitedQueue::peek()
  {
    return (this->q).select(0);
  }
  std::shared_ptr<_module::Thread> ExitedQueue::pop()
  {
    std::shared_ptr<_module::Thread> t = nullptr;
    t = (this->q).select(0);
    (this)->q = (this->q).drop(1);
    return t;
  }
  uint64 ExitedQueue::get__index(std::shared_ptr<_module::Thread> t)
  {
    uint64 i = 0;
    i = (uint64)0;
    while ((i) < ((this)->Length())) {
      if (((this->q).select(i)) == (t)) {
        goto after_0;
      }
      i = (i) + ((uint64)1);
    }
  after_0: ;
    return i;
  }
  void ExitedQueue::remove(std::shared_ptr<_module::Thread> t)
  {
    uint64 _642_i;
    uint64 _out0;
    _out0 = (this)->get__index(t);
    _642_i = _out0;
    if ((_642_i) < ((this)->Length())) {
      (this)->q = ((this->q).take(_642_i)).concatenate(((this->q).drop((_642_i) + ((uint64)1))));
    }
  }
  void ExitedQueue::remove__at(uint64 i)
  {
    (this)->q = ((this->q).take(i)).concatenate(((this->q).drop((i) + ((uint64)1))));
  }

  void RunnableQueue::__ctor()
  {
    (this)->q = DafnySequence<std::shared_ptr<_module::Thread>>::Create({});
  }
  void RunnableQueue::Init(DafnySequence<std::shared_ptr<_module::Thread>> queue)
  {
    (this)->q = queue;
  }
  uint64 RunnableQueue::Length()
  {
    return (uint64)((this->q).size());
  }
  bool RunnableQueue::isEmpty()
  {
    return ((this->q).size()) == (0);
  }
  std::shared_ptr<_module::Thread> RunnableQueue::get__at(uint64 i)
  {
    return (this->q).select(i);
  }
  void RunnableQueue::pushback(std::shared_ptr<_module::Thread> t)
  {
    (this)->q = (this->q).concatenate((DafnySequence<std::shared_ptr<_module::Thread>>::Create({t})));
  }
  std::shared_ptr<_module::Thread> RunnableQueue::peek()
  {
    return (this->q).select(0);
  }
  std::shared_ptr<_module::Thread> RunnableQueue::pop()
  {
    std::shared_ptr<_module::Thread> t = nullptr;
    t = (this->q).select(0);
    (this)->q = (this->q).drop(1);
    return t;
  }
  uint64 RunnableQueue::get__index(std::shared_ptr<_module::Thread> t)
  {
    uint64 i = 0;
    i = (uint64)0;
    while ((i) < ((this)->Length())) {
      if (((this->q).select(i)) == (t)) {
        goto after_1;
      }
      i = (i) + ((uint64)1);
    }
  after_1: ;
    return i;
  }
  void RunnableQueue::remove(std::shared_ptr<_module::Thread> t)
  {
    uint64 _643_i;
    uint64 _out1;
    _out1 = (this)->get__index(t);
    _643_i = _out1;
    if ((_643_i) < ((this)->Length())) {
      (this)->q = ((this->q).take(_643_i)).concatenate(((this->q).drop((_643_i) + ((uint64)1))));
    }
  }
  void RunnableQueue::remove__at(uint64 i)
  {
    (this)->q = ((this->q).take(i)).concatenate(((this->q).drop((i) + ((uint64)1))));
  }

  void SleepingQueue::__ctor()
  {
    (this)->q = DafnySequence<std::shared_ptr<_module::Thread>>::Create({});
  }
  void SleepingQueue::Init(DafnySequence<std::shared_ptr<_module::Thread>> queue)
  {
    (this)->q = queue;
  }
  uint64 SleepingQueue::Length()
  {
    return (uint64)((this->q).size());
  }
  bool SleepingQueue::isEmpty()
  {
    return ((this->q).size()) == (0);
  }
  std::shared_ptr<_module::Thread> SleepingQueue::get__at(uint64 i)
  {
    return (this->q).select(i);
  }
  std::shared_ptr<_module::Thread> SleepingQueue::peek()
  {
    return (this->q).select(0);
  }
  std::shared_ptr<_module::Thread> SleepingQueue::pop()
  {
    std::shared_ptr<_module::Thread> t = nullptr;
    t = (this->q).select(0);
    (this)->q = (this->q).drop(1);
    return t;
  }
  uint64 SleepingQueue::get__index(std::shared_ptr<_module::Thread> t)
  {
    uint64 i = 0;
    i = (uint64)0;
    while ((i) < ((this)->Length())) {
      if (((this->q).select(i)) == (t)) {
        goto after_2;
      }
      i = (i) + ((uint64)1);
    }
  after_2: ;
    return i;
  }
  void SleepingQueue::remove(std::shared_ptr<_module::Thread> t)
  {
    uint64 _644_i;
    uint64 _out2;
    _out2 = (this)->get__index(t);
    _644_i = _out2;
    if ((_644_i) < ((this)->Length())) {
      (this)->q = ((this->q).take(_644_i)).concatenate(((this->q).drop((_644_i) + ((uint64)1))));
    }
  }
  void SleepingQueue::remove__at(uint64 i)
  {
    (this)->q = ((this->q).take(i)).concatenate(((this->q).drop((i) + ((uint64)1))));
  }
  uint64 SleepingQueue::bin__src(uint64 wkt)
  {
    uint64 ind = 0;
    uint64 _645_l;
    uint64 _646_r;
    auto _rhs0 = (uint64)0;
    auto _rhs1 = (uint64)((this->q).size());
    _645_l = _rhs0;
    _646_r = _rhs1;
    while ((_645_l) < (_646_r)) {
      uint64 _647_m;
      _647_m = ((_645_l) + (_646_r)) / ((uint64)2);
      if ((wkt) < ((this->q).select(_647_m)->wakeup__time)) {
        _646_r = _647_m;
      } else if ((wkt) > ((this->q).select(_647_m)->wakeup__time)) {
        _645_l = (_647_m) + ((uint64)1);
      } else {
        ind = _647_m;
        return ind;
      }
    }
    ind = (uint64)-1;
    return ind;
    return ind;
  }
  uint64 SleepingQueue::find__insert__point(uint64 wkt)
  {
    uint64 ind = 0;
    uint64 _648_l;
    uint64 _649_r;
    auto _rhs2 = (uint64)0;
    auto _rhs3 = (uint64)((this->q).size());
    _648_l = _rhs2;
    _649_r = _rhs3;
    while ((_648_l) < (_649_r)) {
      uint64 _650_m;
      _650_m = ((_648_l) + (_649_r)) / ((uint64)2);
      if (((this->q).select(_650_m)->wakeup__time) > (wkt)) {
        _649_r = _650_m;
      } else {
        _648_l = (_650_m) + ((uint64)1);
      }
    }
    ind = _648_l;
    return ind;
  }
  void SleepingQueue::insert(std::shared_ptr<_module::Thread> t)
  {
    uint64 _651_ind;
    uint64 _out3;
    _out3 = (this)->find__insert__point(t->wakeup__time);
    _651_ind = _out3;
    (this)->q = (((this->q).take(_651_ind)).concatenate((DafnySequence<std::shared_ptr<_module::Thread>>::Create({t})))).concatenate(((this->q).drop(_651_ind)));
  }
  DafnySequence<std::shared_ptr<_module::Thread>> SleepingQueue::partition(uint64 wkt)
  {
    DafnySequence<std::shared_ptr<_module::Thread>> smaller = DafnySequence<std::shared_ptr<_module::Thread>>();
    uint64 _652_ind;
    uint64 _out4;
    _out4 = (this)->find__insert__point(wkt);
    _652_ind = _out4;
    smaller = (this->q).take(_652_ind);
    (this)->q = (this->q).drop(_652_ind);
    return smaller;
  }

  void SchedCoop::__ctor()
  {
    (this)->crt__clock = (uint64)0;
    std::shared_ptr<_module::RunnableQueue> _nw0 = std::make_shared<_module::RunnableQueue> ();
    _nw0->__ctor();
    (this)->thread__list = _nw0;
    std::shared_ptr<_module::SleepingQueue> _nw1 = std::make_shared<_module::SleepingQueue> ();
    _nw1->__ctor();
    (this)->sleeping__threads = _nw1;
    std::shared_ptr<_module::ExitedQueue> _nw2 = std::make_shared<_module::ExitedQueue> ();
    _nw2->__ctor();
    (this)->exited__threads = _nw2;
    (this)->threads__started = false;
    std::shared_ptr<_module::Thread> _nw3 = std::make_shared<_module::Thread> ();
    _nw3->NoSched(DafnySequenceFromString("Idle"));
    (this)->idle = _nw3;
    (this)->current = this->idle;
  }
  DafnySequence<std::shared_ptr<_module::Thread>> SchedCoop::get__all__threads__seq()
  {
    return ((this->thread__list->q).concatenate((this->sleeping__threads->q))).concatenate(((((this->current) != (this->idle)) ? (DafnySequence<std::shared_ptr<_module::Thread>>::Create({this->current})) : (DafnySequence<std::shared_ptr<_module::Thread>>::Create({})))));
  }
  void SchedCoop::init()
  {
    (this->idle)->setScheduler(std::shared_ptr<_module::SchedCoop>(this));
  }
  void SchedCoop::thread__add(std::shared_ptr<_module::Thread> t)
  {
    (t)->set__runnable();
    (t)->wakeup__time = (uint64)0;
    (this->thread__list)->pushback(t);
  }
  void SchedCoop::update__sleeping()
  {
    (this)->crt__clock = (this->crt__clock) + ((uint64)1);
    DafnySequence<std::shared_ptr<_module::Thread>> _653_to__wake__up;
    DafnySequence<std::shared_ptr<_module::Thread>> _out5;
    _out5 = (this->sleeping__threads)->partition(this->crt__clock);
    _653_to__wake__up = _out5;
    uint64 _654_i;
    _654_i = (uint64)0;
    while ((_654_i) < ((uint64)((_653_to__wake__up).size()))) {
      std::shared_ptr<_module::Thread> _655_x;
      _655_x = (_653_to__wake__up).select(_654_i);
      (_655_x)->wakeup__time = (uint64)0;
      (_655_x)->set__runnable();
      (this->thread__list)->pushback(_655_x);
      _654_i = (_654_i) + ((uint64)1);
    }
  }
  std::shared_ptr<_module::Thread> SchedCoop::choose__next()
  {
    std::shared_ptr<_module::Thread> next = nullptr;
    std::shared_ptr<_module::Thread> _656_prev;
    _656_prev = this->current;
    if (!((this->thread__list)->isEmpty())) {
      std::shared_ptr<_module::Thread> _out6;
      _out6 = (this->thread__list)->pop();
      next = _out6;
      if ((_656_prev) != (this->idle)) {
        if ((_656_prev)->is__runnable()) {
          (this->thread__list)->pushback(_656_prev);
        }
      }
    } else if ((_656_prev)->is__runnable()) {
      next = _656_prev;
    } else {
      next = this->idle;
    }
    (this)->current = next;
    return next;
  }
  std::shared_ptr<_module::Thread> SchedCoop::schedule()
  {
    std::shared_ptr<_module::Thread> next = nullptr;
    (this)->update__sleeping();
    std::shared_ptr<_module::Thread> _out7;
    _out7 = (this)->choose__next();
    next = _out7;
    return next;
  }
  std::shared_ptr<_module::Thread> SchedCoop::current__sleep(uint64 how__long)
  {
    std::shared_ptr<_module::Thread> next = nullptr;
    auto _obj0 = this->current;
    _obj0->wakeup__time = ((this->crt__clock) + (how__long)) + ((uint64)1);
    auto _obj1 = this->current;
    _obj1->runnable = false;
    (this->sleeping__threads)->insert(this->current);
    next = this->idle;
    (this)->current = next;
    return next;
  }
  void SchedCoop::thread__woken(std::shared_ptr<_module::Thread> t)
  {
    if ((t)->is__runnable()) {
      return;
    }
    if ((this->sleeping__threads->q).contains((t))) {
      (this->sleeping__threads)->remove(t);
    }
    (t)->wakeup__time = (uint64)0;
    (t)->set__runnable();
    if (((t) != (this->current)) || ((t)->is__queueable())) {
      (this->thread__list)->pushback(t);
      (t)->clear__queueable();
    }
  }

}// end of namespace _module 
template <>
struct get_default<std::shared_ptr<_module::class_uint64 > > {
static std::shared_ptr<_module::class_uint64 > call() {
return std::shared_ptr<_module::class_uint64 >();}
};
template <>
struct get_default<std::shared_ptr<_module::Thread > > {
static std::shared_ptr<_module::Thread > call() {
return std::shared_ptr<_module::Thread >();}
};
template <>
struct get_default<std::shared_ptr<_module::ExitedQueue > > {
static std::shared_ptr<_module::ExitedQueue > call() {
return std::shared_ptr<_module::ExitedQueue >();}
};
template <>
struct get_default<std::shared_ptr<_module::RunnableQueue > > {
static std::shared_ptr<_module::RunnableQueue > call() {
return std::shared_ptr<_module::RunnableQueue >();}
};
template <>
struct get_default<std::shared_ptr<_module::SleepingQueue > > {
static std::shared_ptr<_module::SleepingQueue > call() {
return std::shared_ptr<_module::SleepingQueue >();}
};
template <>
struct get_default<std::shared_ptr<_module::SchedCoop > > {
static std::shared_ptr<_module::SchedCoop > call() {
return std::shared_ptr<_module::SchedCoop >();}
};
