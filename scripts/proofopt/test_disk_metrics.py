import json
import tempfile
import unittest
from pathlib import Path
from disk_metrics import Store, js

META={'meta':{'format':{'version':'3.1.0'},'lean':{'githash':'test','version':'test'},'exporter':{'name':'test','version':'test'}}}


def fixture(path,depth=0,variant=False,axiom=False):
    rows=[META,{'in':1,'str':{'pre':0,'str':'T'}},{'in':2,'str':{'pre':0,'str':'base'}},{'in':3,'str':{'pre':0,'str':'root'}},{'in':4,'str':{'pre':0,'str':'binder'}}]
    rows += [{'ie':0,'sort':0},{'ie':1,'const':{'name':1,'us':[]}},{'ie':2,'const':{'name':2,'us':[]}},{'ie':3,'bvar':0}]
    rows += [{'def':{'name':1,'type':0,'value':0,'levelParams':[],'all':[1],'safety':'safe'}},{'axiom' if axiom else 'thm':{'name':2,'type':1,'levelParams':[],**({} if axiom else {'value':1,'all':[2]})}}]
    # Artificial syntax-only DAG: not claimed to be a well-typed Lean proof.
    i=2
    for j in range(depth):
        rows.append({'ie':j+4,'app':{'fn':i,'arg':3}}); i=j+4
    rows.append({'thm':{'name':3,'type':0 if variant else 1,'value':i,'levelParams':[],'all':[3]}})
    path.write_text(''.join(json.dumps(r)+'\n' for r in rows)); return path


class Tests(unittest.TestCase):
    def setUp(self):
        self.t=tempfile.TemporaryDirectory(); self.p=Path(self.t.name); self.s=Store(self.p/'test.db')
    def tearDown(self):
        self.s.db.close(); self.t.cleanup()
    def test_counts(self):
        self.s.ingest('a',fixture(self.p/'a',10)); r=self.s.measure('a',['root'])['union']; self.assertEqual((r['total'],r['dag']['type'],r['dag']['value'],r['dag']['combined']),(3,2,14,14))
    def test_compare(self):
        self.s.ingest('a',fixture(self.p/'a',10)); self.s.ingest('b',fixture(self.p/'b',5)); r=self.s.compare('a','b',['root']); self.assertTrue(r['structural_guard_passed']); self.assertEqual(r['before']['union']['dag']['combined']-r['after']['union']['dag']['combined'],5)
    def test_root_type(self):
        self.s.ingest('a',fixture(self.p/'a')); self.s.ingest('b',fixture(self.p/'b',variant=True)); self.assertFalse(self.s.compare('a','b',['root'])['structural_guard_passed'])
    def test_axiom(self):
        self.s.ingest('a',fixture(self.p/'a')); self.s.ingest('b',fixture(self.p/'b',axiom=True)); self.assertFalse(self.s.compare('a','b',['root'])['structural_guard_passed'])
    def test_missing_root(self):
        self.s.ingest('a',fixture(self.p/'a')); self.assertRaises(ValueError,self.s.measure,'a',['absent'])
    def test_ownership(self):
        p=self.p/'owner'; p.write_text(''.join(json.dumps({'record':'owner','name_parts':[n],'project':n!='T'})+'\n' for n in ('T','base','root'))); self.s.ingest('a',fixture(self.p/'a'),p); self.assertEqual(self.s.measure('a',['root'])['union']['project'],2)
    def test_missing_owner(self):
        p=self.p/'owner'; p.write_text(''); self.s.ingest('a',fixture(self.p/'a'),p); self.assertRaises(ValueError,self.s.measure,'a',['root'])
    def test_transaction_rollback(self):
        p=fixture(self.p/'a'); p.write_text(p.read_text()+'{"ie":999,"app":{"fn":999,"arg":1}}\n'); self.assertRaises(ValueError,self.s.ingest,'a',p); self.assertEqual(self.s.one('SELECT count(*) FROM raw'),0); self.assertEqual(self.s.one('SELECT count(*) FROM pool'),0)
    def test_shared_pool(self):
        p=fixture(self.p/'a',20); self.s.ingest('a',p); n=self.s.one('SELECT count(*) FROM pool'); self.s.ingest('b',p); self.assertEqual(self.s.one('SELECT count(*) FROM pool'),n)
    def test_union(self):
        self.s.ingest('a',fixture(self.p/'a',3)); r=self.s.measure('a',['root','base']); self.assertEqual(r['union']['total'],3); self.assertEqual(r['roots'][1]['total'],2)
    def test_real_export_prefix(self):
        self.s.ingest('a',Path(__file__).with_name('nat_prefix.ndjson')); r=self.s.measure('a',['Nat','Nat.rec']); self.assertEqual((r['union']['total'],r['union']['dag']['combined']),(4,36)); self.assertEqual(r['roots'][0]['dag']['combined'],3)
    def test_deep_dag(self):
        self.s.ingest('a',fixture(self.p/'a',10000)); self.assertEqual(self.s.measure('a',['root'])['union']['dag']['combined'],10004)


if __name__=='__main__': unittest.main()
