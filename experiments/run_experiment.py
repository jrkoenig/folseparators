

import subprocess, os, sys, json, threading, time
from concurrent.futures import ThreadPoolExecutor

class ResultsLogger(object):
    def __init__(self, fn):
        self.lock = threading.Lock()
        self.data = []
        self.last_written = 0
        self.filename = fn
    def add_result(self, result):
        with self.lock:
            self.data.append(result)
            if time.time() > self.last_written + 30:
                self._write()
    def _write(self):
        with open(self.filename, "w") as f:
            json.dump(self.data, f, indent=1)
        self.last_written = time.time()
    def close(self):
        with self.lock:
            self._write()


def run(r, logger):
    try:
        ret = subprocess.run(r['args'], capture_output = True, encoding = 'utf-8', timeout = r['timeout'])
        if ret.returncode == 0:
            last_line = ret.stdout.strip().split("\n")[-1]
            stats = json.loads(last_line)
            r['stats'] = stats
            r['success'] = True
        else:
            r['success'] = False
            r['stderr'] = ret.stderr
        r['killed'] = False
    except subprocess.TimeoutExpired:
        r['killed'] = True
        r['success'] = False

    logger.add_result(r)

def main():
    descs = json.load(open("out/extracted.json"))
    flags = ['--not-incremental']
    N = 1
    logger = ResultsLogger("out/results.baseline.json")

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as executor:
        for d in descs:
            for i in range(N):
                r = {"base": d['base'],
                     "conjecture": d['conjecture'],
                     "index": i,
                     "timeout": 10*60,
                     "args": ['python3', 'learn.py'] + flags + [d['file']]}
                executor.submit(run, r, logger)
    logger.close()

if __name__ == '__main__':
    main()