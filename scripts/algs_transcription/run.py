import sys, random, math, time
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
Ms=[] if len(sys.argv)<2 else [int(x) for x in sys.argv[1].split(',')]
for name,(n,arcs,p,s,t) in INST.items():
    rel=brute_rel(n,arcs,p,s,t)[t]
    for M in Ms:
        t0=time.time()
        L=LeanS(n,arcs,p).exact(s,t,M)
        meanL=sum(z*w for z,w in L.items())
        if s==t or rel==0: Pd=None
        else: Pd=PaperS(n,arcs,p).exact(s,t,M)
        same = (Pd==L) if Pd is not None else 'n/a (paper preprocessing case)'
        print(f"{name:42s} M={M} rel={rel} ({float(rel):.6f}) E[lean]={meanL} unbiased={meanL==rel} support={len(L)} lean==paper dist: {same}  [{time.time()-t0:.1f}s]",flush=True)
