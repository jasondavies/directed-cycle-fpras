"""Extended Algorithm S checks: pool ordering, literal enumeration, arc-order
permutations, and Monte Carlo diagnostics. Run separately from the quick suite.
"""
import sys, random, math, time
sys.setrecursionlimit(100000)
from fractions import Fraction as F
from common import *
from lean_port import LeanS
from paper_port import PaperS
import run as R0
INST=R0.INST
print("== A. fully literal enumeration of LeanS.algS (whole program tree) vs structured exact(), and canon vs non-canon")
for name,(n,arcs,p,s,t) in INST.items():
    for M in (1,2):
        Lp=LeanS(n,arcs,p)
        a=Lp.exact(s,t,M,canon=True); b=Lp.exact(s,t,M,canon=False)
        lit=None
        if M==1 or len(arcs)<=5:
            lit=enumerate_dist(lambda ch:Lp.algS(ch,s,t,M))
        assert a == b, (name, M, "canonical pool order changes the law")
        assert lit is None or lit == a, (name, M, "literal and structured laws differ")
        print(f"{name:42s} M={M} canon==noncanon:{a==b} literal==structured:{'skipped' if lit is None else lit==a}",flush=True)
print("== B. M=3 exact, and random arc-order permutations (M=2)")
rng=random.Random(1)
for name,(n,arcs,p,s,t) in INST.items():
    rel=brute_rel(n,arcs,p,s,t)[t]
    t0=time.time()
    L=LeanS(n,arcs,p).exact(s,t,3); mean=sum(z*w for z,w in L.items())
    P=PaperS(n,arcs,p).exact(s,t,3) if (s!=t and rel>0) else None
    assert mean == rel, (name, "biased M=3 output")
    assert P is None or P == L, (name, "M=3 laws differ")
    print(f"{name:42s} M=3 rel={rel} E[lean]={mean} unbiased={mean==rel} support={len(L)} lean==paper:{'n/a' if P is None else P==L} [{time.time()-t0:.1f}s]",flush=True)
    oks=[];eqs=[]
    for _ in range(4):
        perm=list(range(len(arcs))); rng.shuffle(perm)
        a2=[arcs[i] for i in perm]; p2=[p[i] for i in perm]
        L=LeanS(n,a2,p2).exact(s,t,2); oks.append(sum(z*w for z,w in L.items())==rel)
        if s!=t and rel>0: eqs.append(PaperS(n,a2,p2).exact(s,t,2)==L)
    assert all(oks) and all(eqs), (name, "arc-order comparison failed")
    print(f"{'':42s} 4 random arc orders, M=2: unbiased={oks} lean==paper={eqs}",flush=True)
print("== C. Monte Carlo of the literal LeanS.algS sampler, M=40, 20000 runs")
for name,(n,arcs,p,s,t) in INST.items():
    rel=brute_rel(n,arcs,p,s,t)[t]
    Lp=LeanS(n,arcs,p); ch=Sampler(random.Random(7)); N=20000; M=40
    xs=[float(Lp.algS(ch,s,t,M)) for _ in range(N)]
    mu=sum(xs)/N; sd=math.sqrt(sum((x-mu)**2 for x in xs)/(N-1)); se=sd/math.sqrt(N)
    zsc=(mu-float(rel))/se if se>0 else 0.0
    print(f"{name:42s} rel={float(rel):.6f} mean={mu:.6f} se={se:.6f} z={zsc:+.2f} sd={sd:.4f}",flush=True)
