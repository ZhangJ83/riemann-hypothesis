#!/usr/bin/env python3
"""Disk-backed structural-v1 Lean export measurement. Not a kernel checker."""
import argparse
import hashlib
import json
import sqlite3
from pathlib import Path


def js(x):
    return json.dumps(x, ensure_ascii=False, separators=(',', ':'))


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def nat(x):
    require(type(x) is int and 0 <= x <= 9007199254740991, 'invalid index')
    return x


class Store:
    def __init__(self, path):
        self.db = sqlite3.connect(path)
        self.db.executescript('''
        PRAGMA temp_store=FILE; PRAGMA cache_size=-32768; PRAGMA mmap_size=0;
        CREATE TABLE IF NOT EXISTS pool(id INTEGER PRIMARY KEY, key TEXT UNIQUE NOT NULL);
        CREATE TABLE IF NOT EXISTS child(parent INTEGER, child INTEGER, PRIMARY KEY(parent,child)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS ref(parent INTEGER, name TEXT, PRIMARY KEY(parent,name)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS raw(s TEXT, kind TEXT, n INTEGER, v TEXT, PRIMARY KEY(s,kind,n)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS decl(s TEXT, name TEXT, kind TEXT, type INTEGER, params TEXT, unsafe INTEGER, PRIMARY KEY(s,name)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS val(s TEXT, name TEXT, id INTEGER, PRIMARY KEY(s,name,id)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS kern(s TEXT, name TEXT, dep TEXT, PRIMARY KEY(s,name,dep)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS owner(s TEXT, name TEXT, project INTEGER, PRIMARY KEY(s,name)) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS snapshot(s TEXT PRIMARY KEY, meta TEXT, export_sha TEXT, owner_sha TEXT, lines INTEGER);
        ''')

    def q(self, sql, args=()):
        return self.db.execute(sql, args)

    def one(self, sql, args=()):
        row = self.q(sql, args).fetchone()
        require(row is not None, 'missing reference: ' + str(args))
        return row[0]

    def intern(self, data, children=(), refs=()):
        k = js(data)
        cur = self.q('INSERT OR IGNORE INTO pool(key) VALUES (?)', (k,))
        if cur.rowcount:
            i = cur.lastrowid
            self.db.executemany('INSERT OR IGNORE INTO child VALUES (?,?)', ((i,c) for c in children))
            self.db.executemany('INSERT OR IGNORE INTO ref VALUES (?,?)', ((i,r) for r in refs))
            return i
        return self.one('SELECT id FROM pool WHERE key=?', (k,))

    def ingest(self, s, path, owner=None):
        require(not self.q('SELECT 1 FROM snapshot WHERE s=?', (s,)).fetchone(), 'snapshot exists')
        def put(k, i, v):
            self.q('INSERT INTO raw VALUES (?,?,?,?)', (s,k,nat(i),js(v)))
        def get(k, i):
            return json.loads(self.one('SELECT v FROM raw WHERE s=? AND kind=? AND n=?', (s,k,nat(i))))
        def N(i): return js(get('n',i))
        def L(i): return get('l',i)
        def E(i): return get('e',i)
        def declaration(t,d):
            name=N(d['name']); require(name!='[]','anonymous declaration')
            unsafe=d.get('isUnsafe') is True or (t=='def' and d.get('safety')!='safe')
            self.q('INSERT INTO decl VALUES (?,?,?,?,?,?)',(s,name,t,E(d['type']),js([N(i) for i in d['levelParams']]),int(unsafe)))
            vals=[E(d['value'])] if t in ('thm','def','opaque') else []
            deps=[N(i) for i in d['all']] if t in ('thm','def','opaque','ind','rec') else []
            if t=='ind': deps += [N(i) for i in d['ctors']]
            if t=='ctor': deps.append(N(d['induct']))
            if t=='rec':
                for r in d['rules']: deps.append(N(r['ctor'])); vals.append(E(r['rhs']))
            if t=='quot': deps += [js(x.split('.')) for x in ('Quot','Quot.mk','Quot.lift','Quot.ind','Eq')]
            self.db.executemany('INSERT OR IGNORE INTO val VALUES (?,?,?)',((s,name,i) for i in vals))
            self.db.executemany('INSERT OR IGNORE INTO kern VALUES (?,?,?)',((s,name,x) for x in deps if x!=name))
        h=hashlib.sha256(); meta=None; count=0
        with self.db:
            put('n',0,[]); put('l',0,self.intern(['level','zero']))
            with open(path,'rb') as f:
                for count,line in enumerate(f,1):
                    h.update(line)
                    try:
                        r=json.loads(line); require(isinstance(r,dict),'expected record')
                        if count==1:
                            require(set(r)=={'meta'},'missing metadata'); meta=r['meta']
                            version=meta['format']['version']; require(version in ('3.0.0','3.1.0'),'unsupported format')
                            require(all(isinstance(meta[k][p],str) and meta[k][p] for k,p in [('lean','githash'),('lean','version'),('exporter','name'),('exporter','version')]),'missing identity'); continue
                        ix=next((x for x in ('in','il','ie') if x in r),None)
                        tags=set(r)-({ix} if ix else set()); require(len(tags)==1,'ambiguous record'); t=tags.pop(); v=r[t]
                        if ix=='in':
                            a=v['str'] if t=='str' else nat(v['i']) if t=='num' else None
                            require(a is not None and (t!='str' or isinstance(a,str)),'bad name'); put('n',r[ix],get('n',v['pre'])+[a]); continue
                        if ix=='il':
                            if t=='succ': a=[L(v)]
                            elif t=='param': a=[N(v)]
                            elif t in ('max','imax'): require(len(v)==2,'bad level arity'); a=[L(i) for i in v]
                            else: raise ValueError('unknown level '+t)
                            put('l',r[ix],self.intern(['level',t,*a])); continue
                        if ix=='ie':
                            c=[]; refs=[]
                            if t=='mdata': put('e',r[ix],E(v['expr'])); continue
                            if t=='bvar': a=[nat(v)]
                            elif t=='sort': a=[L(v)]
                            elif t=='const': refs=[N(v['name'])]; a=[refs[0],[L(i) for i in v['us']]]
                            elif t=='app': c=[E(v['fn']),E(v['arg'])]; a=c
                            elif t in ('lam','forallE'):
                                N(v['name']); require(v['binderInfo'] in ('default','implicit','strictImplicit','instImplicit'),'bad binder'); c=[E(v['type']),E(v['body'])]; a=[v['binderInfo'],*c]
                            elif t=='letE':
                                N(v['name']); require(type(v['nondep']) is bool,'bad let'); c=[E(v[x]) for x in ('type','value','body')]; a=c
                            elif t=='proj': refs=[N(v['typeName'])]; c=[E(v['struct'])]; a=[refs[0],nat(v['idx']),*c]
                            elif t=='natVal': require(isinstance(v,str) and v.isascii() and v.isdecimal() and (v=='0' or not v.startswith('0')),'bad numeral'); a=[v]; refs=[js(['Nat'])]
                            elif t=='strVal': require(isinstance(v,str),'bad string'); a=[v]; refs=[js(x.split('.')) for x in ('Char.ofNat','String.ofList')]
                            else: raise ValueError('unknown expression '+t)
                            put('e',r[ix],self.intern(['expr',t,*a],c,refs)); continue
                        if t=='inductive':
                            fields=('inductiveVals','constructorVals','recursorVals') if version=='3.0.0' else ('types','ctors','recs')
                            for k,field in zip(('ind','ctor','rec'),fields):
                                for d in v[field]: declaration(k,d)
                        elif t in ('axiom','def','thm','opaque','quot'):
                            for d in (v if isinstance(v,list) and version=='3.0.0' else [v]): declaration(t,d)
                        else: raise ValueError('unknown declaration '+t)
                    except (ValueError,KeyError,TypeError,sqlite3.IntegrityError) as exc:
                        raise ValueError(f'{path}:{count}: {exc}') from exc
            require(meta is not None and self.one('SELECT count(*) FROM decl WHERE s=?',(s,))>0,'empty export')
            oh=None
            if owner:
                digest=hashlib.sha256()
                with open(owner,'rb') as f:
                    for line in f:
                        digest.update(line); r=json.loads(line); require(r['record']=='owner','bad owner record')
                        parts=r['name_parts']; require(isinstance(parts,list) and parts,'bad owner name')
                        for p in parts:
                            if not isinstance(p,str): nat(p)
                        if r['project'] is not None:
                            require(type(r['project']) is bool,'bad owner flag'); self.q('INSERT INTO owner VALUES (?,?,?)',(s,js(parts),int(r['project'])))
                oh=digest.hexdigest()
            self.q('INSERT INTO snapshot VALUES (?,?,?,?,?)',(s,js(meta),h.hexdigest(),oh,count))
            # Raw indices are snapshot-local and never needed for measurement.
            self.q('DELETE FROM raw WHERE s=?',(s,))
        return h.hexdigest()

    def measure(self,s,roots):
        meta,sha,oh,lines=self.q('SELECT meta,export_sha,owner_sha,lines FROM snapshot WHERE s=?',(s,)).fetchone()
        names=[js(x.split('.') if isinstance(x,str) else x) for x in roots]
        require(names and len(set(names))==len(names),'empty/duplicate roots')
        def closure(names):
            self.db.executescript('DROP TABLE IF EXISTS temp.live; CREATE TEMP TABLE live(kind INTEGER,id TEXT,PRIMARY KEY(kind,id)) WITHOUT ROWID; DROP TABLE IF EXISTS temp.root; CREATE TEMP TABLE root(name TEXT PRIMARY KEY) WITHOUT ROWID;')
            self.db.executemany('INSERT INTO root VALUES (?)',((n,) for n in names))
            self.q('''INSERT INTO live WITH RECURSIVE reach(k,i) AS (
              SELECT 0,name FROM root
              UNION SELECT 1,CAST(d.type AS TEXT) FROM reach r JOIN decl d ON r.k=0 AND d.s=? AND d.name=r.i
              UNION SELECT 1,CAST(v.id AS TEXT) FROM reach r JOIN val v ON r.k=0 AND v.s=? AND v.name=r.i
              UNION SELECT 0,k.dep FROM reach r JOIN kern k ON r.k=0 AND k.s=? AND k.name=r.i
              UNION SELECT 1,CAST(c.child AS TEXT) FROM reach r JOIN child c ON r.k=1 AND c.parent=CAST(r.i AS INTEGER)
              UNION SELECT 0,f.name FROM reach r JOIN ref f ON r.k=1 AND f.parent=CAST(r.i AS INTEGER)
            ) SELECT k,i FROM reach''',(s,s,s))
            require(not self.q('SELECT l.id FROM live l LEFT JOIN decl d ON d.s=? AND d.name=l.id WHERE l.kind=0 AND d.name IS NULL LIMIT 1',(s,)).fetchone(),'unresolved reachable declaration')
            if oh: require(not self.q('SELECT l.id FROM live l LEFT JOIN owner o ON o.s=? AND o.name=l.id WHERE l.kind=0 AND o.name IS NULL LIMIT 1',(s,)).fetchone(),'missing ownership')
            def size(value,project=False):
                own=' JOIN owner o ON o.s=d.s AND o.name=d.name AND o.project=1' if project else ''
                seed=('SELECT v.id FROM live l JOIN decl d ON l.kind=0 AND d.name=l.id AND d.s=?'+own+' JOIN val v ON v.s=d.s AND v.name=d.name' if value else 'SELECT d.type FROM live l JOIN decl d ON l.kind=0 AND d.name=l.id AND d.s=?'+own)
                return self.one('WITH RECURSIVE r(i) AS ('+seed+' UNION SELECT c.child FROM r JOIN child c ON c.parent=r.i) SELECT count(*) FROM r',(s,))
            def combined(project=False):
                own=' JOIN owner o ON o.s=d.s AND o.name=d.name AND o.project=1' if project else ''
                seed=' FROM live l JOIN decl d ON l.kind=0 AND d.name=l.id AND d.s=?'+own
                return self.one('WITH RECURSIVE r(i) AS (SELECT d.type'+seed+' UNION SELECT v.id'+seed+' JOIN val v ON v.s=d.s AND v.name=d.name UNION SELECT c.child FROM r JOIN child c ON c.parent=r.i) SELECT count(*) FROM r',(s,s))
            ax=[r[0] for r in self.q("SELECT d.name FROM live l JOIN decl d ON l.kind=0 AND d.name=l.id AND d.s=? WHERE d.kind='axiom' ORDER BY d.name",(s,))]
            unsafe=[r[0] for r in self.q('SELECT d.name FROM live l JOIN decl d ON l.kind=0 AND d.name=l.id AND d.s=? WHERE d.unsafe=1 ORDER BY d.name',(s,))]
            allowed={js(x.split('.')) for x in ('propext','Quot.sound','Classical.choice')}
            return dict(total=self.one('SELECT count(*) FROM live WHERE kind=0'),project=self.one('SELECT count(*) FROM live l JOIN owner o ON l.kind=0 AND o.s=? AND o.name=l.id AND o.project=1',(s,)) if oh else None,axioms=ax,unexpected_axioms=[a for a in ax if a not in allowed],unsafe=unsafe,dag=dict(type=size(False),value=size(True),combined=combined()),project_dag=dict(type=size(False,True),value=size(True,True),combined=combined(True)) if oh else None)
        return dict(normalization='structural-v1',backend='sqlite-v1',meta=json.loads(meta),export_sha256=sha,ownership_sha256=oh,lines=lines,roots=[dict(name=json.loads(n),**closure([n])) for n in names],union=closure(names),kernel_verified=False)

    def compare(self,a,b,roots):
        x,y=self.measure(a,roots),self.measure(b,roots)
        require(x['meta']==y['meta'],'incompatible export metadata')
        require(bool(x['ownership_sha256'])==bool(y['ownership_sha256']),'incompatible owner mode')
        consistent=not self.q('SELECT 1 FROM owner x JOIN owner y ON x.name=y.name WHERE x.s=? AND y.s=? AND x.project<>y.project LIMIT 1',(a,b)).fetchone()
        same=True
        for root in roots:
            n=js(root.split('.') if isinstance(root,str) else root)
            rows=[self.q('SELECT kind,type,params FROM decl WHERE s=? AND name=?',(s,n)).fetchone() for s in (a,b)]
            same &= rows[0]==rows[1]
        pairs=list(zip(x['roots'],y['roots']))+[(x['union'],y['union'])]
        guard=same and consistent and all(not set(q['axioms'])-set(p['axioms']) and not q['unexpected_axioms'] and not q['unsafe'] for p,q in pairs)
        def delta(p,q):
            def metric(a,b): return None if a is None or b is None else dict(before=a,after=b,reduced=a-b,fraction=(a-b)/a if a else None)
            return dict(project=metric(p['project'],q['project']),all_declarations=metric(p['total'],q['total']),dag=metric(p['dag']['combined'],q['dag']['combined']),value_dag=metric(p['dag']['value'],q['dag']['value']),project_dag=metric(p['project_dag']['combined'] if p['project_dag'] else None,q['project_dag']['combined'] if q['project_dag'] else None))
        return dict(before=x,after=y,root_types_same=same,ownership_consistent=consistent,per_root=[dict(name=p['name'],**delta(p,q)) for p,q in pairs[:-1]],union=delta(*pairs[-1]),structural_guard_passed=guard,kernel_verified=False)


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('db'); p.add_argument('mode',choices=['measure','compare']); p.add_argument('files',nargs='+'); p.add_argument('--roots',nargs='+',required=True); a=p.parse_args()
    require(len(a.files)==(2 if a.mode=='measure' else 4),'expected EXPORT OWNER pairs (use - for no owner)')
    require(not Path(a.db).exists(),'database must be new'); s=Store(a.db)
    for i in range(0,len(a.files),2): s.ingest(str(i),a.files[i],None if a.files[i+1]=='-' else a.files[i+1])
    out=s.measure('0',a.roots) if a.mode=='measure' else s.compare('0','2',a.roots)
    print(json.dumps(out,ensure_ascii=False,indent=2)); return 1 if out.get('structural_guard_passed') is False else 0


if __name__=='__main__':
    raise SystemExit(main())
