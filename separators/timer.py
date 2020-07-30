# Copyright 2020 Stanford University

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import time, math, z3
from typing import Any, Sequence, Union

class TimeoutException(Exception):
    pass

class Timer(object):
    # Limit is time in seconds
    def __init__(self, limit:float):
        self._elapsed: float = 0.0
        self.limit: float = limit
        self.start: float = 0.0
        self.level: int = 0
        
    def __enter__(self) -> 'Timer':
        if self.level == 0:
            self.start = time.time()
        self.level += 1
        return self

    def __exit__(self, type: Exception, value: Any, traceback: Any) -> None:
        if type is TimeoutException:
            return
        assert self.level > 0
        self.level -= 1
        if self.level == 0:
            self._elapsed += time.time() - self.start
        self.check_time()

    def remaining(self) -> float:
        return self.limit - self.elapsed()

    def elapsed(self) -> float:
        if self.level > 0:
            return self._elapsed + (time.time() - self.start)
        else:
            return self._elapsed

    def check_time(self) -> None:
        if self.remaining() < 0:
            raise TimeoutException()
    
    def solver_check(self, solver: Union[z3.Solver, z3.Optimize], *args: z3.ExprRef) -> z3.CheckSatResult:
        assert self.level > 0 # only allow sat while this timer is active
        
        remaining = self.remaining()
        if remaining < 0.1: # within 100ms of timeout
            raise TimeoutException()
        
        solver.set('timeout', int(remaining * 1000)) # solver timeout is in ms
        result = solver.check(*args)
        solver.set('timeout', 0)
        
        if self.remaining() < 0.1: # within 100ms of timeout
            raise TimeoutException()
        return result

class UnlimitedTimer(Timer):
    def __init__(self) -> None:
        Timer.__init__(self, float(10000000))
    # def solver_check(self, solver: Union[z3.Solver, z3.Optimize], *args: z3.ExprRef) -> z3.CheckSatResult:
    #     return solver.check(*args)
    # def check_time(self) -> None: pass
    # def remaining(self) -> float: return float("+inf")
