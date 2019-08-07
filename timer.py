

import time, math, z3

class TimeoutException(Exception):
    pass

class Timer(object):
    # Limit is time in seconds
    def __init__(self, limit):
        self._elapsed = 0.0
        self.limit = limit
        self.start = 0.0
        self.running = False
        
    def __enter__(self):
        assert not self.running
        self.start = time.time()
        self.running = True
        return self

    def __exit__(self, type, value, traceback):
        if type is TimeoutException:
            return
        assert self.running
        self._elapsed += time.time() - self.start
        self.running = False
        self.check_time()

    def remaining(self):
        return self.limit - self.elapsed()

    def elapsed(self):
        if self.running:
            return self._elapsed + (time.time() - self.start)
        else:
            return self._elapsed

    def check_time(self):
        if self.remaining() < 0:
            raise TimeoutException()
    
    def solver_check(self, solver):
        assert self.running # only allow sat while this timer is active
        
        remaining = self.remaining()
        if remaining < 0.1: # within 100ms of timeout
            raise TimeoutException()
        
        solver.set(timeout = int(remaining * 1000)) # solver timeout is in ms
        result = solver.check()
        solver.set(timeout = 0)
        
        if self.remaining() < 0.1: # within 100ms of timeout
            raise TimeoutException()
        return result

class UnlimitedTimer(Timer):
    def __init__(self):
        Timer.__init__(self, float("+inf"))