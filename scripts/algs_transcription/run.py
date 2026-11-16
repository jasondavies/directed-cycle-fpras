"""Exact finite comparisons of the Lean and paper ports.

Run from any directory. A mismatch exits nonzero; results are recorded in
validation/algs-transcription-results.json. These are finite checks, not a
proof connecting either Python port to Lean or to the published algorithm.
"""
import argparse
import json
from pathlib import Path
import time
from fractions import Fraction as F
from common import *
from lean_port import LeanS
from paper_port import PaperS
h=F(1,2)
INST={
 # name: (n, arcs, p, s, t)
 'path2+parallel': (3,[(0,1),(0,1),(1,2)],[h,F(1,3),F(2,3)],0,2),
 'diamond': (4,[(0,1),(0,2),(1,3),(2,3),(1,2)],[h,F(1,3),F(2,3),h,F(3,4)],0,3),
 'diamond+backarcs+loop': (4,[(0,1),(1,0),(0,2),(1,1),(1,3),(2,3),(2,1),(3,0)],[h,F(1,3),F(1,3),h,F(2,3),h,F(3,4),h],0,3),
 'unreachable+p1': (5,[(4,0),(0,1),(1,2),(0,2),(2,3),(4,3),(1,3),(3,1)],[h,F(1),h,F(1,3),F(1),h,F(1,4),h],0,3),
 'parallel-into-t,p=1 mix': (4,[(0,1),(0,1),(1,2),(2,1),(1,3),(1,3),(2,3),(2,2)],[F(1,3),h,F(1),h,F(1,5),h,F(1,3),F(1)],0,3),
 '5v-cycle': (5,[(0,1),(1,2),(2,0),(2,3),(1,3),(3,4),(0,4),(4,1)],[h,h,h,F(1,3),F(1,4),F(2,3),F(1,10),h],0,4),
 't-first(order rev)': (4,[(2,3),(1,3),(1,2),(0,2),(0,1),(0,3)],[h,F(2,3),F(3,4),F(1,3),h,F(1,10)],0,3),
 't unreachable': (3,[(0,1),(2,1)],[h,h],0,2),
 's=t': (2,[(0,1)],[h],0,0),
 'all p=1': (3,[(0,1),(1,2),(0,2)],[F(1),F(1),F(1)],0,2),
 'intermediate t (t resolved before others)': (4,[(0,3),(0,1),(1,2),(2,3)],[F(9,10),F(1,10),h,h],0,3),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("budgets", nargs="?", default="1", help="positive sample counts, e.g. 1,2,3")
    args = parser.parse_args()
    try:
        budgets = [int(value) for value in args.budgets.split(",")]
        if not budgets or any(value <= 0 for value in budgets):
            raise ValueError
    except ValueError:
        parser.error("budgets must be comma-separated positive integers")
    records = []
    for name, (n, arcs, p, s, t) in INST.items():
        reliability = brute_rel(n, arcs, p, s, t)[t]
        for budget in budgets:
            started = time.monotonic()
            lean = LeanS(n, arcs, p).exact(s, t, budget)
            mean = sum(value * mass for value, mass in lean.items())
            # The paper handles these two cases before entering Algorithm S.
            if s == t:
                paper = {F(1): F(1)}
            elif reliability == 0:
                paper = {F(0): F(1)}
            else:
                paper = PaperS(n, arcs, p).exact(s, t, budget)
            if sum(lean.values()) != 1 or any(mass < 0 for mass in lean.values()):
                raise AssertionError(f"{name}, M={budget}: invalid output law")
            if mean != reliability:
                raise AssertionError(f"{name}, M={budget}: mean {mean} != reliability {reliability}")
            if lean != paper:
                raise AssertionError(f"{name}, M={budget}: the output distributions differ")
            records.append({"case": name, "samples": budget,
                            "reliability": str(reliability), "mean": str(mean),
                            "support_size": len(lean), "laws_equal": True})
            print(f"{name}: M={budget} passed ({time.monotonic() - started:.1f}s)", flush=True)
    report = {"scope": "Exact finite comparison of two Python ports, including paper preprocessing cases",
              "cases": records}
    root = Path(__file__).resolve().parents[2]
    (root / "validation").mkdir(exist_ok=True)
    (root / "validation/algs-transcription-results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(records)} exact Algorithm S comparisons", flush=True)


if __name__ == "__main__":
    main()
