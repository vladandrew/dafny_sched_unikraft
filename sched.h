// Dafny program sched.dfy compiled into a Cpp header file
#pragma once
#include "DafnyRuntime.h"
namespace _System  {
}// end of namespace _System  declarations
namespace _module  {
  class class_uint64;
  class Thread;
  class ExitedQueue;
  class RunnableQueue;
  class SleepingQueue;
  class SchedCoop;
}// end of namespace _module  declarations
namespace _System  {
}// end of namespace _System  datatype declarations
namespace _module  {
}// end of namespace _module  datatype declarations
namespace _System  {
}// end of namespace _System  class declarations
namespace _module  {
  class class_uint64 {
    public:
    // Default constructor
    class_uint64() {}
    static uint64 get_Default() {
      return 0;
    }
  };
  class Thread {
    public:
    // Default constructor
    Thread() {}
    DafnySequence<char> name = DafnySequence<char>();
    uint64 stack = 0;
    uint64 ctx = 0;
    bool runnable = false;
    bool queueable = false;
    bool exited = false;
    uint16 flags = 0;
    uint64 wakeup__time = 0;
    bool detached = false;
    std::shared_ptr<_module::SchedCoop> sched = nullptr;
    void __ctor(DafnySequence<char> n, std::shared_ptr<_module::SchedCoop> s);
    void NoName(std::shared_ptr<_module::SchedCoop> s);
    void NoSched(DafnySequence<char> n);
    void setScheduler(std::shared_ptr<_module::SchedCoop> s);
    bool is__runnable();void set__runnable();
    void clear__runnable();
    bool is__exited();void set__exited();
    void clear__exited();
    bool is__queueable();void set__queueable();
    void clear__queueable();
    void set__wakeup__time(uint64 delta);
  };
  class ExitedQueue {
    public:
    // Default constructor
    ExitedQueue() {}
    DafnySequence<std::shared_ptr<_module::Thread>> q = DafnySequence<std::shared_ptr<_module::Thread>>();
    void __ctor();
    void Init(DafnySequence<std::shared_ptr<_module::Thread>> queue);
    uint64 Length();bool isEmpty();std::shared_ptr<_module::Thread> get__at(uint64 i);void pushback(std::shared_ptr<_module::Thread> t);
    std::shared_ptr<_module::Thread> peek();std::shared_ptr<_module::Thread> pop();
    uint64 get__index(std::shared_ptr<_module::Thread> t);
    void remove(std::shared_ptr<_module::Thread> t);
    void remove__at(uint64 i);
  };
  class RunnableQueue {
    public:
    // Default constructor
    RunnableQueue() {}
    DafnySequence<std::shared_ptr<_module::Thread>> q = DafnySequence<std::shared_ptr<_module::Thread>>();
    void __ctor();
    void Init(DafnySequence<std::shared_ptr<_module::Thread>> queue);
    uint64 Length();bool isEmpty();std::shared_ptr<_module::Thread> get__at(uint64 i);void pushback(std::shared_ptr<_module::Thread> t);
    std::shared_ptr<_module::Thread> peek();std::shared_ptr<_module::Thread> pop();
    uint64 get__index(std::shared_ptr<_module::Thread> t);
    void remove(std::shared_ptr<_module::Thread> t);
    void remove__at(uint64 i);
  };
  class SleepingQueue {
    public:
    // Default constructor
    SleepingQueue() {}
    DafnySequence<std::shared_ptr<_module::Thread>> q = DafnySequence<std::shared_ptr<_module::Thread>>();
    void __ctor();
    void Init(DafnySequence<std::shared_ptr<_module::Thread>> queue);
    uint64 Length();bool isEmpty();std::shared_ptr<_module::Thread> get__at(uint64 i);std::shared_ptr<_module::Thread> peek();std::shared_ptr<_module::Thread> pop();
    uint64 get__index(std::shared_ptr<_module::Thread> t);
    void remove(std::shared_ptr<_module::Thread> t);
    void remove__at(uint64 i);
    uint64 bin__src(uint64 wkt);
    uint64 find__insert__point(uint64 wkt);
    void insert(std::shared_ptr<_module::Thread> t);
    DafnySequence<std::shared_ptr<_module::Thread>> partition(uint64 wkt);
  };
  class SchedCoop {
    public:
    // Default constructor
    SchedCoop() {}
    std::shared_ptr<_module::Thread> current = nullptr;
    uint64 crt__clock = 0;
    std::shared_ptr<_module::RunnableQueue> thread__list = nullptr;
    std::shared_ptr<_module::SleepingQueue> sleeping__threads = nullptr;
    std::shared_ptr<_module::ExitedQueue> exited__threads = nullptr;
    std::shared_ptr<_module::Thread> idle = nullptr;
    bool threads__started = false;
    void __ctor();
    DafnySequence<std::shared_ptr<_module::Thread>> get__all__threads__seq();void init();
    void thread__add(std::shared_ptr<_module::Thread> t);
    void update__sleeping();
    std::shared_ptr<_module::Thread> choose__next();
    std::shared_ptr<_module::Thread> schedule();
    std::shared_ptr<_module::Thread> current__sleep(uint64 how__long);
    void thread__woken(std::shared_ptr<_module::Thread> t);
  };
}// end of namespace _module  class declarations
