
import argparse, json, os, os.path, re
from typing import *

def natsortkey(s: str) -> Tuple[Union[int, str], ...]:
    ll: List[Union[int, str]] = list()
    for x in re.split(r'(\d+)', s):
        if re.match(r'(\d+)', x):
            ll.append(int(x))
        else:
            ll.append(x)
    return tuple(ll)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=str, nargs='+')
    parser.add_argument("--limit", type=float, default=3600.0)
    args = parser.parse_args()

    results: Dict[str, Dict[str, float]] = {}
    columns: List[str] = []
    for fname in args.input:
        base = os.path.splitext(os.path.basename(fname))[0]
        columns.append(base)
        data = json.load(open(fname, 'r'))
        for result in data:
            results.setdefault(result['conjecture'], {})[base] = result['stats']['separation_time']
    print(','.join(['problem', *columns]))
    for problem in sorted(results.keys(), key=natsortkey):
        rs = results[problem]
        print(','.join([problem, *(str(rs[c]) for c in columns)]))
    
main()