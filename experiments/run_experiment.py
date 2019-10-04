
import subprocess, os, sys, json, threading, time, argparse
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
        # double for both timers and add 60 seconds to account for timing errors
        ret = subprocess.run(r['args'], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             encoding = 'utf-8', timeout = 2*r['timeout'] + 60)
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--descriptions", metavar="IN", default = "out/extracted.json", help="descriptions of conjectures to learn")
    parser.add_argument("--output", "-o", metavar="OUT", default = "out/results.json", help="output file to write")
    parser.add_argument("--timeout", metavar='T', type=float, default = 10*60, help="timeout for each of learning and separation (seconds)")
    parser.add_argument("--count", metavar='N', type=int, default = 1, help="number of times to learn each conjecture")
    parser.add_argument("args", nargs=argparse.REMAINDER, help="arguments to learner")
    
    args = parser.parse_args()
    descs = json.load(open(args.descriptions))
    logger = ResultsLogger(args.output)
    a =  args.args if args.args[0] != '--' else args.args[1:]

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as executor:
        for d in descs:
            for i in range(args.count):
                r = {"base": d['base'],
                     "conjecture": d['conjecture'],
                     "index": i,
                     "timeout": args.timeout,
                     "args": ['python3', '-m', 'separators'] + a + ["--timeout", str(int(args.timeout)), d['file']]}
                executor.submit(run, r, logger)
    logger.close()

if __name__ == '__main__':
    main()
