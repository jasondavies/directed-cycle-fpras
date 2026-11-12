# Line-by-line port of DirectedCycleFPRAS/AlgorithmS.lean (NOT of the paper).
from fractions import Fraction as F
from common import *

def normLaw(w, d):
    # w: list of (outcome, weight); d default outcome
    if all(x>=0 for _,x in w) and sum(x for _,x in w)>0:
        tot=sum(x for _,x in w)
        return [(o,x/tot) for o,x in w]
    return [(o, F(1) if o==d else F(0)) for o,_ in w]

class LeanS:
    def __init__(self, n, arcs, p):
        self.n=n; self.arcs=arcs; self.p=p; self.m=len(arcs)
        self.arcOrder=list(range(self.m))
    def source(self,e): return self.arcs[e][0]
    def target(self,e): return self.arcs[e][1]
    def arcBefore(self,e1,e): return self.arcOrder.index(e1) < self.arcOrder.index(e)
    def cutAt(self,R,u,e): return self.source(e)==u and self.target(e) not in R
    def firstOpenWeight(self,R,u,e):
        if self.cutAt(R,u,e):
            r=self.p[e]
            for e1 in range(self.m):
                if self.cutAt(R,u,e1) and self.arcBefore(e1,e): r*=(1-self.p[e1])
            return r
        return F(0)
    def gammaS(self,R,u): return sum(self.firstOpenWeight(R,u,e) for e in range(self.m))
    def preState(self,R,u,j,e):
        if self.cutAt(R,u,e):
            if e==j: return True
            if self.arcBefore(e,j): return False
            return None
        return None
    def coin(self,x): return normLaw([(True,x),(False,1-x)], False)
    def sScan(self,ch,R,pre,z,flag,l,D,st):
        if not l: return (D,st)
        e=l[0]; l=l[1:]
        if self.source(e)==z and self.target(e) not in D:
            pe=pre(e)
            o = ch.choose(self.coin(self.p[e])) if pe is None else pe
            if o:
                return self.sScan(ch,R,pre,z,flag,l,D|{self.target(e)},
                                  [(self.target(e), flag and (self.target(e) not in R))]+st)
            else: return self.sScan(ch,R,pre,z,flag,l,D,st)
        else: return self.sScan(ch,R,pre,z,flag,l,D,st)
    def sDfs(self,ch,R,pre,v,f,D,st):
        if f==0: return None
        if not st: return None
        (z,flag)=st[0]; st=st[1:]
        if z==v: return D if flag else None
        D2,st2=self.sScan(ch,R,pre,z,flag,self.arcOrder,D,st)
        return self.sDfs(ch,R,pre,v,f-1,D2,st2)
    def sIter(self,ch,R,qh,pools,M,v):
        w=[(None,F(0))]+[(u, qh[u]*self.gammaS(R,u) if u in R else F(0)) for u in range(self.n)]
        o=ch.choose(normLaw(w,None))
        if o is None: return None
        u=o
        i=ch.choose(normLaw([(i, F(1) if i<len(pools[u]) else F(0)) for i in range(M+1)],0))
        j=ch.choose(normLaw([(None,F(0))]+[(e,self.firstOpenWeight(R,u,e)) for e in range(self.m)],None))
        if j is None: return None
        D0 = pools[u][i] if i<len(pools[u]) else frozenset()
        return self.sDfs(ch,R,lambda e:self.preState(R,u,j,e),v,self.n+1,D0,[(u,True)])
    def sGenerate(self,ch,R,qh,pools,M,v,i):
        if i==0: return (0,())
        acc=self.sGenerate(ch,R,qh,pools,M,v,i-1)
        o=self.sIter(ch,R,qh,pools,M,v)
        return acc if o is None else (acc[0]+1,(o,)+acc[1])
    def phiS(self,R,qh): return sum((qh[u]*self.gammaS(R,u) if u in R else F(0)) for u in range(self.n))
    def argmax_arc(self,R,qh):
        best=None
        for e in self.arcOrder:
            if self.source(e) in R and self.target(e) not in R:
                val=qh[self.source(e)]*self.p[e]
                if best is None or val>best[1]: best=(e,val)   # first maximal
        return None if best is None else best[0]
    def divM(self,x,M): return F(0) if M==0 else x/M   # Lean real division by zero is 0
    def sRounds(self,ch,t,M,f,R,qh,pools):
        if f==0: return qh[t]
        if t in R: return qh[t]
        e=self.argmax_arc(R,qh)
        if e is None: return F(0)
        if qh[self.source(e)]*self.p[e] <= 0: return F(0)
        v=self.target(e)
        res=self.sGenerate(ch,R,qh,pools,M,v,M)
        qh2=list(qh); qh2[v]=self.divM(self.phiS(R,qh)*res[0],M)
        pools2=list(pools); pools2[v]=res[1]
        return self.sRounds(ch,t,M,f-1,R|{v},tuple(qh2),tuple(pools2))
    def algS(self,ch,s,t,M):
        return self.sRounds(ch,t,M,self.n,frozenset({s}),
            tuple(F(1) if u==s else F(0) for u in range(self.n)),
            tuple((frozenset({s}),) if u==s else () for u in range(self.n)))

    # ---- exact output distribution (structured to avoid enumerating the whole tree at once)
    def exact(self,s,t,M,canon=True):
        memo={}
        def gen_dist(R,qh,pools,v):
            it=enumerate_dist(lambda ch:self.sIter(ch,R,qh,pools,M,v))
            d={(0,()):F(1)}
            for _ in range(M):
                nd={}
                for acc,pa in d.items():
                    for o,po in it.items():
                        a2 = acc if o is None else (acc[0]+1,(o,)+acc[1])
                        if canon: a2=(a2[0],tuple(sorted(a2[1],key=sorted)))
                        nd[a2]=nd.get(a2,0)+pa*po
                d=nd
            return d
        def rounds(f,R,qh,pools):
            key=(f,R,qh,pools)
            if key in memo: return memo[key]
            if f==0 or t in R: r={qh[t]:F(1)}
            else:
                e=self.argmax_arc(R,qh)
                if e is None or qh[self.source(e)]*self.p[e]<=0: r={F(0):F(1)}
                else:
                    v=self.target(e); r={}
                    for res,pr in gen_dist(R,qh,pools,v).items():
                        qh2=list(qh); qh2[v]=self.divM(self.phiS(R,qh)*res[0],M)
                        pools2=list(pools); pools2[v]=res[1]
                        for z,pz in rounds(f-1,R|{v},tuple(qh2),tuple(pools2)).items():
                            r[z]=r.get(z,0)+pr*pz
            memo[key]=r; return r
        return rounds(self.n,frozenset({s}),
            tuple(F(1) if u==s else F(0) for u in range(self.n)),
            tuple((frozenset({s}),) if u==s else () for u in range(self.n)))
