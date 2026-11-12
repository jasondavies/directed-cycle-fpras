# Independent port of the PAPER's pseudocode (Algorithms 1, 2, S), written without
# reference to the Lean structure: full DFS run with parent pointers, cut arcs at u
# drawn jointly by enumerating all assignments conditional on >=1 open.
from fractions import Fraction as F
from collections import Counter
import itertools, math
from common import *

class PaperS:
    def __init__(self,n,arcs,p): self.n=n; self.arcs=arcs; self.p=p
    def out(self,z): return [e for e,(a,b) in enumerate(self.arcs) if a==z]
    def cut_from(self,R,u): return [e for e in self.out(u) if self.arcs[e][1] not in R]
    def gamma(self,R,u):
        r=F(1)
        for e in self.cut_from(R,u): r*=1-self.p[e]
        return 1-r
    def iteration(self,ch,R,qh,pools,v):
        Phi=sum(qh[u]*self.gamma(R,u) for u in R)
        u=ch.choose([(x,qh[x]*self.gamma(R,x)/Phi) for x in sorted(R)])
        pool=pools[u]; cnt=Counter(pool)
        A=ch.choose([(a,F(c,len(pool))) for a,c in cnt.items()])
        cut=self.cut_from(R,u); g=self.gamma(R,u)
        joint=[]
        for bits in itertools.product([False,True],repeat=len(cut)):
            if not any(bits): continue
            w=F(1)
            for e,b in zip(cut,bits): w*= self.p[e] if b else 1-self.p[e]
            joint.append((bits,w/g))
        forced=dict(zip(cut,ch.choose(joint)))
        # DFS(u,A), run to completion
        D=set(A); S=[u]; parent={}; record=None
        while S:
            z=S.pop()
            if z==v:
                x=z; ok=True
                while x!=u:
                    x=parent[x]
                    if x!=u and x in R: ok=False
                if ok: record=frozenset(D)
            for e in self.out(z):
                y=self.arcs[e][1]
                if y in D: continue
                if z==u and e in forced: is_open=forced[e]
                else: is_open=ch.choose([(True,self.p[e]),(False,1-self.p[e])])
                if is_open: D.add(y); parent[y]=z; S.append(y)
        return record
    def exact(self,s,t,M):
        memo={}
        def run(R,qh,pools):
            key=(R,tuple(sorted(qh.items())),tuple(sorted((k,v) for k,v in pools.items())))
            if key in memo: return memo[key]
            if t in R: return {qh[t]:F(1)}
            cutarcs=[e for e,(a,b) in enumerate(self.arcs) if a in R and b not in R]
            best=None
            for e in cutarcs:
                val=qh[self.arcs[e][0]]*self.p[e]
                if best is None or val>best[0]: best=(val,e)
            if best is None or best[0]==0: return {F(0):F(1)}
            v=self.arcs[best[1]][1]
            Phi=sum(qh[u]*self.gamma(R,u) for u in R)
            it=enumerate_dist(lambda ch:self.iteration(ch,R,qh,pools,v))
            d={():F(1)}
            for _ in range(M):
                nd={}
                for recs,pa in d.items():
                    for o,po in it.items():
                        r2=recs if o is None else tuple(sorted(recs+(o,),key=sorted))
                        nd[r2]=nd.get(r2,0)+pa*po
                d=nd
            r={}
            for recs,pr in d.items():
                qh2=dict(qh); qh2[v]=Phi*len(recs)/M
                pools2=dict(pools); pools2[v]=recs
                for z,pz in run(R|{v},qh2,pools2).items(): r[z]=r.get(z,0)+pr*pz
            memo[key]=r; return r
        return run(frozenset({s}),{s:F(1)},{s:(frozenset({s}),)})
