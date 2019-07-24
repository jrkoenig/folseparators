
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
        # add 60 seconds for hard cutoff to account for timing errors
        ret = subprocess.run(r['args'], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             encoding = 'utf-8', timeout = r['timeout'] + 60)
        if ret.returncode == 0:
            last_line = ret.stdout.strip().split("\n")[-1]
            stats = json.loads(last_line)
            r['stats'] = stats
            r['success'] = stats['success']
        else:
            r['success'] = False
            r['stderr'] = ret.stderr
        r['killed'] = False
    except subprocess.TimeoutExpired:
        r['killed'] = True
        r['success'] = False
    except Exception as e:
        print(e)
    logger.add_result(r)

def main():
    descs = json.load(open("out/extracted.json"))
    flags = ['--logic=fol']
    N = 1
    timeout = 10*60
    logger = ResultsLogger("out/results.split.json")

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as executor:
        for d in descs:
            for i in range(N):
                r = {"base": d['base'],
                     "conjecture": d['conjecture'],
                     "index": i,
                     "timeout": timeout,
                     "args": ['python3', 'learn.py'] + flags + ["--timeout", str(timeout), d['file']]}
                executor.submit(run, r, logger)
    logger.close()

if __name__ == '__main__':
    main()
