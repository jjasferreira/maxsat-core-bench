import argparse
import sys
import time
import os
import subprocess
from pysat.formula import WCNF, CNF
from pysat.solvers import SolverNames, Solver
from pysat.card import CardEnc, EncType

CORE = False
SOLVER = "g3" #"cadical103"
VERBOSE = False

def read_formula(path: str) -> WCNF:
    try:
        open(path, 'r')
    except FileNotFoundError:
        print("ERROR: File not found:", path)
        return
    ϕ = WCNF(from_file=path)
    if VERBOSE:
        print("ϕ.path =", path)
        print("ϕ.nv =", ϕ.nv)
        print("ϕ.nc =", len(ϕ.hard + ϕ.soft))
        print("|ϕ.hard| =", len(ϕ.hard))
        print("|ϕ.soft| =", len(ϕ.soft))
        print("-" * 20)
    return ϕ

def extract_proof(ϕ: WCNF) -> tuple[int, set[int]]:
    uc = []
    rsi = set(range(len(ϕ.soft)))
    os.makedirs("tmp", exist_ok=True)
    while True:
        s = Solver(name=SOLVER, with_proof=True)
        s.append_formula(ϕ.hard + [ϕ.soft[i] for i in rsi])
        st = s.solve()
        if VERBOSE: print("|ϕ| =", len(ϕ.hard + [ϕ.soft[i] for i in rsi])); print("st =", st)
        if st: break
        p = s.get_proof()
        tmp = ϕ.copy()
        tmp.soft = [ϕ.soft[i] for i in rsi]
        tmp.unweighted().to_file("tmp/ϕ.cnf")
        with open("tmp/p.drat", "w") as f: f.write('\n'.join(str(l) for l in p))
        subprocess.run(["./drat-trim", "tmp/ϕ.cnf", "tmp/p.drat", "-c", "tmp/c.cnf"], capture_output=True, text=True)
        c = CNF(from_file="tmp/c.cnf").clauses
        uc.append(c)
        for ω in c:
            for i in list(rsi):
                if set(ω) == set(ϕ.soft[i]):
                    rsi.remove(i)
                    break
        if VERBOSE: print("|c| =", len(c)); print("-" * 20)
    if CORE: print("λ1 =", len(uc)); print("uc =", [len(c) for c in uc])
    print("=" * 20)
    return len(uc), rsi

def extract_assumptions(wcnf: WCNF) -> tuple[int, set[int]]:
    unsat_core_sizes = ""; unsat_core_number = 0 # new
    cores = []
    remaining_soft_ids = set(range(len(wcnf.soft)))
    while remaining_soft_ids:
        # Add relaxation variables to soft clauses (s_i v r_i)
        nvars = wcnf.nv
        rvars = []
        rvars_to_soft_ids = {}
        rsoft = []
        for i in sorted(remaining_soft_ids):
            nvars += 1
            rvars.append(nvars)
            rvars_to_soft_ids[nvars] = i
            rsoft.append(wcnf.soft[i] + [nvars])
        #if VERBOSE: print("remaining_soft_ids:", remaining_soft_ids); print("rvars:", rvars); print("rvars_to_soft_ids:", rvars_to_soft_ids); print("rsoft:", rsoft)
        # Extract cores by negating the relaxation variables
        s = Solver(name=SOLVER)
        s.append_formula(wcnf.hard + rsoft)
        ass = [-r for r in rvars]
        st = s.solve(assumptions=ass)
        #if VERBOSE: print("ass", ass); print("st:", st)
        if st:
            #print("SAT model:", s.get_model()); print("-" * 100)
            break
        core = sorted(s.get_core(), reverse=True)
        #if VERBOSE: print("c:", core) 
        core_ids = [rvars_to_soft_ids[abs(rlit)] for rlit in core]
        cores.append(core_ids)
        if VERBOSE:
            print("UNSAT core ids:", core_ids)
            print("UNSAT cores:", cores)
            print("------------------------------")
        remaining_soft_ids.difference_update(core_ids)
        unsat_core_sizes += str(len(core)) + " "; unsat_core_number += 1 # new
    if VERBOSE:
        print("UNSAT core sizes:", unsat_core_sizes) # new
        print("UNSAT core number:", unsat_core_number) # new
    return len(cores), remaining_soft_ids

def linear_search(ϕ: WCNF, λ: int, rsi: set[int]) -> int:
    # Add relaxation variables to soft clauses involved in cores (c_i v r_i)
    bv = []; b = ϕ.nv
    for i in range(len(ϕ.soft)):
        if i not in rsi:
            b += 1
            bv.append(b)
            ϕ.soft[i].append(b)

    # Perform linear search from lower bound upwards AtMost(sum rvars <= k)
    while True:
        ϕb = CardEnc.atmost(encoding=EncType.totalizer, lits=bv, bound=λ, top_id=b)
        b = ϕb.nv
        s = Solver(name=SOLVER)
        s.append_formula(ϕ.hard + ϕ.soft + ϕb.clauses)
        st = s.solve()
        if VERBOSE: print("bv =", bv); print("λ =", λ); print("|ϕ| =", len(ϕ.hard + ϕ.soft + ϕb.clauses)); print("st =", st)
        if st: break
        λ += 1
        if VERBOSE: print("-" * 20)
    if CORE: print("λ2 =", λ)
    print("=" * 20)
    return λ

def msu3_proof(ϕ: WCNF) -> int:
    uc = []
    os.makedirs("tmp", exist_ok=True)
    while True:
        s = Solver(name=SOLVER, with_proof=True)
        s.append_formula(ϕ.hard + ϕ.soft)
        st = s.solve()
        if VERBOSE: print("|ϕ| =", len(ϕ.hard + ϕ.soft)); print("st =", st)
        if st: break
        p = s.get_proof()
        ϕ.copy().unweighted().to_file("tmp/ϕ.cnf")
        with open("tmp/p.drat", "w") as f: f.write('\n'.join(str(l) for l in p))
        subprocess.run(["./drat-trim", "tmp/ϕ.cnf", "tmp/p.drat", "-c", "tmp/c.cnf"], capture_output=True, text=True)
        c = CNF(from_file="tmp/c.cnf").clauses
        ϕ.soft = [sc for sc in ϕ.soft if set(sc) not in [set(ω) for ω in c]]
        uc.append(c)
        if VERBOSE: print("|c| =", len(c)); print("-" * 20)
    if CORE: print("λ1 =", len(uc)); ucs = [len(c) for c in uc]; print("ucs =", ucs); print("aucs =", sum(ucs) / len(ucs) if ucs else 0)
    print("=" * 20)

    bv = []; b = ϕ.nv
    for c in uc:
        for ω in c:
            if any(set(ω) == set(hc) for hc in ϕ.hard): continue
            b += 1
            bv.append(b)
            ϕ.soft.append(list(ω) + [b])

    λ = len(uc)
    while True:
        ϕb = CardEnc.atmost(encoding=EncType.totalizer, lits=bv, bound=λ, top_id=b)
        b = ϕb.nv
        s = Solver(name=SOLVER, with_proof=True)
        s.append_formula(ϕ.hard + ϕ.soft + ϕb.clauses)
        st = s.solve()
        if VERBOSE: print("|bv| =", len(bv)); print("λ =", λ); print("|ϕ| =", len(ϕ.hard + ϕ.soft + ϕb.clauses)); print("st =", st)
        if st: break
        λ += 1
        p = s.get_proof()
        ϕt = ϕ.copy().unweighted()
        ϕt.clauses += ϕb; ϕt.nv = b
        ϕt.to_file("tmp/ϕ.cnf")
        with open("tmp/p.drat", "w") as f: f.write('\n'.join(str(l) for l in p))
        subprocess.run(["./drat-trim", "tmp/ϕ.cnf", "tmp/p.drat", "-c", "tmp/c.cnf"], capture_output=True, text=True)
        c = CNF(from_file="tmp/c.cnf").clauses
        if CORE: uc.append(c)
        for ω in c:
            if any(set(ω) == set(hc) for hc in ϕ.hard): continue
            if all(abs(lit) <= ϕ.nv for lit in ω):
                b += 1
                ϕ.soft = [sc for sc in ϕ.soft if set(ω) != set(sc)]
                ϕ.soft.append(list(ω) + [b])
                bv.append(b)
        if VERBOSE: print("|c| =", len(c)); print("-" * 20)
    if CORE: print("λ2 =", λ); ucs = [len(c) for c in uc]; print("ucs =", ucs); print("aucs =", sum(ucs) / len(ucs) if ucs else 0)
    print("=" * 20)
    return λ

def msu3_assumptions(ϕ: WCNF) -> int:
    uc = []
    soft = {}
    uch = []
    r = ϕ.nv
    for sc in ϕ.soft:
        r += 1
        soft[r] = list(sc) + [r]
    for hc in ϕ.hard:
        r += 1
        hc.append(r)
    while True:
        s = Solver(name=SOLVER)
        s.append_formula(ϕ.hard + list(soft.values()))
        st = s.solve(assumptions=[-lit for lit in range(ϕ.nv+1, r+1)])
        if VERBOSE: print("|ϕ| =", len(ϕ.hard) + len(soft)); print("st =", st)
        if st: break
        c = []; ch = 0
        for idx in s.get_core():
            if -idx in soft:
                c.append(soft[-idx])
                del soft[-idx]
            else:
                ch += 1
        uc.append(c); uch.append(ch)
        if VERBOSE: print("|c| =", len(c) + ch); print("-" * 20)
    if CORE: print("λ1 =", len(uc)); ucs = [len(uc[i]) + (uch[i] if i < len(uch) else 0) for i in range(len(uc))]; print("ucs =", ucs); print("aucs =", sum(ucs) / len(ucs) if ucs else 0)
    print("=" * 20)
    
    bv = []; b = r
    for c in uc:
        for ω in c:
            b += 1
            bv.append(b)
            ω.insert(-1, b)
            soft[ω[-1]] = ω

    λ = len(uc)
    while True:
        ϕb = CardEnc.atmost(encoding=EncType.totalizer, lits=bv, bound=λ, top_id=b)
        b = ϕb.nv
        s = Solver(name=SOLVER)
        s.append_formula(ϕ.hard + list(soft.values()) + ϕb.clauses)
        st = s.solve(assumptions=[-lit for lit in range(ϕ.nv+1, r+1)])
        if VERBOSE: print("|bv| =", len(bv)); print("λ =", λ); print("st =", st)
        if st: break  
        λ += 1
        c = s.get_core()
        if CORE: uc.append(c)
        for idx in c:
            if -idx in soft:
                if any(lit in bv for lit in soft[-idx]): continue
                b += 1
                soft[-idx].insert(-1, b)
                bv.append(b)
        if VERBOSE: print("|c| =", len(c)); print("-" * 20)
    if CORE: print("λ2 =", λ); ucs = [len(uc[i]) + (uch[i] if i < len(uch) else 0) for i in range(len(uc))]; print("ucs =", ucs); print("aucs =", sum(ucs) / len(ucs) if ucs else 0)
    print("=" * 20)
    return λ
    
def main() -> None:
    parser = argparse.ArgumentParser(description="maxsat-core-bench by José João Ferreira")
    parser.add_argument("-c", "--core", action="store_true", help="print extracted UNSAT cores analysis")
    parser.add_argument("-f", "--file", required=True, help="path to the input WCNF formula")
    parser.add_argument("-p", "--proof", action="store_true", help="use proof-based extraction (DRAT-trim) instead of assumption-based (default)")
    parser.add_argument("-s", "--solver", default="g3", help="SAT solver name to use - e.g., g3 (default), cadical")
    parser.add_argument("-t", "--time", action="store_true", help="track and print total execution time")
    parser.add_argument("-v", "--verbose", action="store_true", help="enable verbose output for debugging")
    args = parser.parse_args()
    global CORE, SOLVER, VERBOSE
    CORE = args.core
    SOLVER = args.solver.lower()
    VERBOSE = args.verbose

    ϕ = read_formula(args.file)
    if args.time: start = time.time()
    #if args.proof:
    #    λ, rsi = extract_proof(ϕ)
    #    λ = linear_search(ϕ, λ, rsi)
    #else:
    #    λ, rsi = extract_assumptions(ϕ)
    #    λ = linear_search(ϕ, λ, rsi)
    λ = msu3_proof(ϕ) if args.proof else msu3_assumptions(ϕ)
    if args.time: print(f"t = {time.time() - start:.3f}s")

if __name__ == "__main__":
    main()