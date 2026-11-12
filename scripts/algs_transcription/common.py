from fractions import Fraction as F
import random, itertools

class Replay:
    """Enumerate all executions of a randomized procedure exactly."""
    def __init__(self, prefix): self.prefix=prefix; self.pos=0; self.prob=F(1); self.branch=None
    def choose(self, items):
        items=[(o,w) for o,w in items if w!=0]
        if self.pos < len(self.prefix):
            i=self.prefix[self.pos]
        else:
            i=0; self.prefix.append(0)
        self.pos+=1
        self.last=(len(items))
        self.sizes.append(len(items)) if hasattr(self,'sizes') else None
        o,w=items[i]; self.prob*=w; return o

def enumerate_dist(proc):
    """proc(ch) -> hashable. Returns dict outcome->prob."""
    dist={}
    prefix=[]
    while True:
        ch=Replay(prefix); ch.sizes=[]
        val=proc(ch)
        assert ch.pos==len(prefix)
        dist[val]=dist.get(val,0)+ch.prob
        # advance
        sizes=ch.sizes
        k=len(prefix)-1
        while k>=0 and prefix[k]+1>=sizes[k]: k-=1
        if k<0: break
        prefix=prefix[:k]+[prefix[k]+1]
    assert sum(dist.values())==1, sum(dist.values())
    return dist

class Sampler:
    def __init__(self, rng): self.rng=rng
    def choose(self, items):
        x=self.rng.random(); acc=0.0
        last=None
        for o,w in items:
            if w==0: continue
            acc+=float(w); last=o
            if x<acc: return o
        return last

def brute_rel(n, arcs, p, s, t, target=None):
    """exact Pr[s reaches each vertex]"""
    m=len(arcs); q=[F(0)]*n
    for bits in itertools.product([0,1],repeat=m):
        w=F(1)
        for e in range(m): w*= p[e] if bits[e] else 1-p[e]
        if w==0: continue
        seen={s}; stack=[s]
        while stack:
            z=stack.pop()
            for e,(a,b) in enumerate(arcs):
                if bits[e] and a==z and b not in seen: seen.add(b); stack.append(b)
        for v in seen: q[v]+=w
    return q
