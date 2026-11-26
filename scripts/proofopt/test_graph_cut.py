import random, unittest
from graph_cut import Graph, rank


def graph(rows):
    g=Graph()
    for name, kind, project, t, v, k in rows:
        g.add(dict(record='decl',name=name,kind=kind,module='P' if project else 'E',project=project,type=t,value=v,kernel=k),{'P'})
    return g

class TestCut(unittest.TestCase):
    def check_all(self,g,roots):
        roots=[g.ids[x] for x in roots]; rows,summary=rank(g,roots); before=g.reach(roots)
        self.assertEqual(summary['live'],sum(before))
        self.assertEqual(summary['project'],sum(g.meta[i][2] for i,b in enumerate(before) if b))
        for row in rows:
            after=g.reach(roots,g.ids[row['name']]); lost=[i for i,b in enumerate(before) if b and not after[i]]
            self.assertEqual((row['project_cut'],row['all_cut']),(sum(g.meta[i][2] for i in lost),len(lost)))
        return rows
    def test_shared_and_protected(self):
        g=graph([('R','thm',True,[],['A','B'],[]),('A','thm',True,['X'],['X','Y','Z'],[]),('B','thm',True,[],['Z'],[]),('X','def',True,[],[],[]),('Y','def',True,[],[],[]),('Z','def',True,[],[],[])])
        rows=self.check_all(g,['R']); self.assertEqual([(x['name'],x['project_cut']) for x in rows],[('A',1),('B',0)])
    def test_external_and_cycle(self):
        g=graph([('R','thm',True,[],['A'],[]),('A','thm',True,[],['E'],[]),('E','def',False,[],['B'],[]),('B','thm',True,[],['E'],[])])
        rows=self.check_all(g,['R']); self.assertEqual((rows[0]['name'],rows[0]['project_cut'],rows[0]['all_cut']),('A',1,2))
    def test_missing(self):
        g=graph([('R','thm',True,[],['missing'],[])])
        with self.assertRaises(ValueError): rank(g,[g.ids['R']])
    def test_random(self):
        rng=random.Random(117)
        for trial in range(200):
            names=[str(i) for i in range(rng.randrange(4,35))]
            rows=[]
            for name in names:
                refs=lambda: rng.sample(names,rng.randrange(min(5,len(names))))
                rows.append((name,rng.choice(['thm','thm','def']),rng.choice([True,True,False]),refs(),refs(),refs()))
            self.check_all(graph(rows),names[:2])

if __name__=='__main__': unittest.main()
