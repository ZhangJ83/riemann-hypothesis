"""Reference-graph cut ranking, not certified proof rewriting."""
import argparse, gzip, hashlib, json, time
from array import array
from collections import Counter
from pathlib import Path
try:
    from orjson import loads
except ImportError:
    loads = json.loads

class Graph:
    def __init__(self):
        self.ids, self.names, self.meta = {}, [], []
        self.start, self.split, self.end = (array('q') for _ in range(3))
        self.edges = array('I')
    def intern(self, name):
        if name not in self.ids:
            self.ids[name] = len(self.names)
            self.names.append(name); self.meta.append(None)
            for a in (self.start,self.split,self.end): a.append(-1)
        return self.ids[name]
    def add(self,row,modules):
        i=self.intern(row['name'])
        if row['record']!='decl' or self.meta[i] is not None: raise ValueError('duplicate or invalid declaration')
        if row['project']!=(row['module'] in modules): raise ValueError('ownership mismatch')
        self.meta[i]=(row['module'],row['kind'],row['project'])
        protected=set(row['type'])|set(row['kernel'])
        self.start[i]=len(self.edges)
        self.edges.extend(self.intern(x) for x in sorted(protected))
        self.split[i]=len(self.edges)
        self.edges.extend(self.intern(x) for x in sorted(set(row['value'])-protected))
        self.end[i]=len(self.edges)
    def reach(self,roots,cut=None):
        seen=bytearray(len(self.names)); todo=list(roots)
        for i in todo: seen[i]=1
        while todo:
            i=todo.pop(); end=self.split[i] if i==cut else self.end[i]
            for j in range(self.start[i],end):
                v=self.edges[j]
                if not seen[v]: seen[v]=1; todo.append(v)
        return seen
    def load(self,path,modules,expected):
        h=hashlib.sha256()
        with gzip.open(path,'rb') as f:
            line=next(f); h.update(line); header=loads(line)
            if (header.get('schema'),header.get('record'),header.get('measurement'))!=(1,'header','kernel-reference-graph'): raise ValueError('unsupported header')
            for line in f: h.update(line); self.add(loads(line),modules)
        if h.hexdigest()!=expected: raise ValueError('digest mismatch')
        return header

def rank(g,roots):
    import numpy as np
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import depth_first_order
    live=[i for i,b in enumerate(g.reach(roots)) if b]
    missing=[g.names[i] for i in live if g.meta[i] is None]
    if missing: raise ValueError(f'{len(missing)} unresolved reachable names: {missing[:20]}')
    index={i:j for j,i in enumerate(live)}
    candidates=[i for i in live if g.meta[i][1:]==('thm',True) and i not in roots and g.split[i]<g.end[i]]
    gates={i:len(live)+j for j,i in enumerate(candidates)}; source=len(live)+len(gates)
    ix,ptr=array('I'),array('q',[0])
    for i in live:
        end=g.split[i] if i in gates else g.end[i]
        ix.extend(index[g.edges[j]] for j in range(g.start[i],end))
        if i in gates: ix.append(gates[i])
        ptr.append(len(ix))
    for i in candidates:
        ix.extend(index[g.edges[j]] for j in range(g.split[i],g.end[i])); ptr.append(len(ix))
    ix.extend(index[i] for i in roots); ptr.append(len(ix)); n=source+1
    a=csr_matrix((np.ones(len(ix),dtype=np.int8),np.asarray(ix),np.asarray(ptr)),shape=(n,n))
    order,parent=depth_first_order(a,source,directed=True,return_predecessors=True)
    if len(order)!=n: raise ValueError('split graph lost nodes')
    children=[[] for _ in range(n)]
    for v in order[1:]: children[int(parent[v])].append(int(v))
    post,todo=[],[(source,False)]
    while todo:
        v,done=todo.pop()
        if done: post.append(v)
        else: todo.append((v,True)); todo.extend((w,False) for w in reversed(children[v]))
    rpo=post[::-1]; pos=[0]*n
    for j,v in enumerate(rpo): pos[v]=j
    pred=a.transpose().tocsr(); ip,pi=pred.indptr,pred.indices
    dom=[-1]*n; dom[source]=source
    def intersect(x,y):
        while x!=y:
            while pos[x]>pos[y]: x=dom[x]
            while pos[y]>pos[x]: y=dom[y]
        return x
    rounds=0; changed=True
    while changed:
        rounds+=1; changed=False
        for v in rpo[1:]:
            d=-1
            for k in range(ip[v],ip[v+1]):
                p=int(pi[k])
                if dom[p]!=-1: d=p if d==-1 else intersect(d,p)
            if d!=-1 and dom[v]!=d: dom[v]=d; changed=True
    project=[int(g.meta[i][2]) for i in live]+[0]*(n-len(live)); total=[1]*len(live)+[0]*(n-len(live))
    for v in reversed(rpo[1:]):
        if dom[v]<0 or pos[dom[v]]>=pos[v]: raise ValueError('invalid dominator tree')
        project[dom[v]]+=project[v]; total[dom[v]]+=total[v]
    rows=[dict(name=g.names[i],module=g.meta[i][0],project_cut=project[gates[i]],all_cut=total[gates[i]],value_only_edges=g.end[i]-g.split[i]) for i in candidates]
    rows.sort(key=lambda x:(-x['project_cut'],-x['all_cut'],x['name']))
    return rows,dict(live=len(live),project=project[source],split_nodes=n,split_edges=len(ix),passes=rounds,kinds=dict(Counter(g.meta[i][1] for i in live)),axioms=sorted(g.names[i] for i in live if g.meta[i][1]=='axiom'))

def analyze(path,modules,expected,top=20):
    start=time.monotonic(); g=Graph()
    header=g.load(path,set(Path(modules).read_text().splitlines()),expected)
    print("loaded",len(g.names),len(g.edges),flush=True); roots=[g.ids[x] for x in header["roots"]]; rows,union=rank(g,roots); before=g.reach(roots); checks=[]
    for row in rows[:top]:
        after=g.reach(roots,g.ids[row['name']]); lost=[i for i,b in enumerate(before) if b and not after[i]]
        if sum(g.meta[i][2] for i in lost)!=row['project_cut'] or len(lost)!=row['all_cut']: raise ValueError('cut verification failed: '+row['name'])
        checks.append(dict(**row,lost_project_sample=sorted(g.names[i] for i in lost if g.meta[i][2])[:15]))
    individual={}
    for i in roots:
        seen=g.reach([i]); individual[g.names[i]]=dict(all=sum(seen),project=sum(g.meta[j][2] for j,b in enumerate(seen) if b))
    return dict(schema=1,metric='reference graph; not kernel DAG or certified compression',graph_sha256=expected,declarations=sum(m is not None for m in g.meta),unresolved_environment_names=sum(m is None for m in g.meta),edges=len(g.edges),project_declarations=sum(m[2] for m in g.meta if m),union=union,individual=individual,candidates=len(rows),positive_project_candidates=sum(x['project_cut']>0 for x in rows),top=checks,elapsed_seconds=round(time.monotonic()-start,3))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for x in ('graph','modules','sha256','output'): p.add_argument(x)
    p.add_argument('--top',type=int,default=20); a=p.parse_args()
    Path(a.output).write_text(json.dumps(analyze(a.graph,a.modules,a.sha256,a.top),indent=2,ensure_ascii=False)+'\n')
