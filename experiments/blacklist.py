import json, sys, argparse, re
from collections import defaultdict
from typing import *


comment = re.compile("^\w*;.*$")
def strip_comments(s: str) -> str:
    return "\n".join(l for l in s.splitlines() if not comment.match(l))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=argparse.FileType('r'))
    parser.add_argument("--output", type=argparse.FileType('w'), default = "conjectures/benchmark.json")
    args = parser.parse_args()
    descs = json.load(args.input)
    
    # Blacklisted because they are all isomorphic
    blacklist = ['tlb100', 'tlb101', 'tlb102', 'tlb103', 'tlb104', 'tlb105', 'tlb106', 'tlb107', 'tlb108', 'tlb109', 'tlb110', 'tlb111', 'tlb112', 'tlb113', 'tlb114', 'tlb115', 'tlb116', 'tlb117', 'tlb118', 'tlb119', 'tlb120', 'tlb121', 'tlb122', 'tlb123', 'tlb124', 'tlb125', 'tlb126', 'tlb127', 'tlb128', 'tlb129', 'tlb130', 'tlb131', 'tlb132', 'tlb133', 'tlb134', 'tlb135', 'tlb136', 'tlb137', 'tlb138', 'tlb139', 'tlb140', 'tlb141', 'tlb142', 'tlb143', 'tlb144', 'tlb145', 'tlb146', 'tlb147', 'tlb148', 'tlb149', 'tlb150', 'tlb151', 'tlb152', 'tlb153', 'tlb154', 'tlb155', 'tlb156', 'tlb157', 'tlb158', 'tlb159', 'tlb160', 'tlb161', 'tlb162', 'tlb163', 'tlb164', 'tlb165', 'tlb166', 'tlb167', 'tlb168', 'tlb169', 'tlb170', 'tlb171', 'tlb172', 'tlb173', 'tlb174', 'tlb175', 'tlb176', 'tlb177', 'tlb178', 'tlb179', 'tlb180', 'tlb181', 'tlb182', 'tlb183', 'tlb184', 'tlb185', 'tlb186', 'tlb187', 'tlb188', 'tlb189', 'tlb190', 'tlb191', 'tlb192', 'tlb193', 'tlb194', 'tlb195', 'tlb196', 'tlb197', 'tlb198', 'tlb199', 'tlb200', 'tlb201', 'tlb202', 'tlb203', 'tlb204', 'tlb205', 'tlb206', 'tlb207', 'tlb208', 'tlb209', 'tlb210', 'tlb211', 'tlb212', 'tlb213', 'tlb214', 'tlb215', 'tlb216', 'tlb217', 'tlb218', 'tlb219', 'tlb220', 'tlb221', 'tlb222', 'tlb223', 'tlb224', 'tlb225', 'tlb226', 'tlb227', 'tlb228', 'tlb229', 'tlb230', 'tlb231', 'tlb232', 'tlb233', 'tlb234', 'tlb235', 'tlb236', 'tlb237', 'tlb238', 'tlb239', 'tlb240', 'tlb241', 'tlb242', 'tlb243', 'tlb244', 'tlb245', 'tlb246', 'tlb247', 'tlb248', 'tlb249', 'tlb25', 'tlb250', 'tlb251', 'tlb252', 'tlb253', 'tlb254', 'tlb255', 'tlb256', 'tlb257', 'tlb258', 'tlb259', 'tlb26', 'tlb260', 'tlb261', 'tlb262', 'tlb263', 'tlb264', 'tlb265', 'tlb266', 'tlb267', 'tlb268', 'tlb269', 'tlb27', 'tlb270', 'tlb271', 'tlb272', 'tlb273', 'tlb274', 'tlb275', 'tlb276', 'tlb277', 'tlb278', 'tlb279', 'tlb28', 'tlb280', 'tlb281', 'tlb282', 'tlb283', 'tlb284', 'tlb285', 'tlb286', 'tlb287', 'tlb288', 'tlb289', 'tlb29', 'tlb290', 'tlb291', 'tlb292', 'tlb293', 'tlb294', 'tlb295', 'tlb296', 'tlb297', 'tlb298', 'tlb299', 'tlb30', 'tlb300', 'tlb31', 'tlb32', 'tlb33', 'tlb34', 'tlb35', 'tlb36', 'tlb37', 'tlb38', 'tlb39', 'tlb40', 'tlb41', 'tlb42', 'tlb43', 'tlb44', 'tlb45', 'tlb46', 'tlb47', 'tlb48', 'tlb49', 'tlb50', 'tlb51', 'tlb52', 'tlb53', 'tlb54', 'tlb55', 'tlb56', 'tlb57', 'tlb58', 'tlb59', 'tlb60', 'tlb61', 'tlb62', 'tlb63', 'tlb64', 'tlb65', 'tlb66', 'tlb67', 'tlb68', 'tlb69', 'tlb70', 'tlb71', 'tlb72', 'tlb73', 'tlb74', 'tlb75', 'tlb76', 'tlb77', 'tlb78', 'tlb79', 'tlb80', 'tlb81', 'tlb82', 'tlb83', 'tlb84', 'tlb85', 'tlb86', 'tlb87', 'tlb88', 'tlb89', 'tlb90', 'tlb91', 'tlb92', 'tlb93', 'tlb94', 'tlb95', 'tlb96', 'tlb97', 'tlb98', 'tlb99']
    descs = [d for d in descs if not (d['base'] == 'tlb_pcrel' and d['conjecture'] in blacklist)]
    
    files_by_contents: DefaultDict[str, List[Any]] = defaultdict(list)
    for d in descs:
        #print(strip_comments(open(d['file']).read()))
        files_by_contents[strip_comments(open(d['file']).read())].append(d)

    descs = [sorted(ds, key = lambda x: x['file'])[0] for contents, ds in files_by_contents.items()]
    json.dump(descs, args.output, indent=1)
main()