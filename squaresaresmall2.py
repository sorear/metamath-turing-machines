"""Turing machine for conjecturing that all squares are less than 5."""
import dsl
g = dsl.DSL()

for m in g.main():
    for w in m.whileloop(g.less(g.read('b'), g.lit(5))):
        w.set('b', g.mul(g.read('a'), g.read('a')))
        w.set('a', g.add(g.read('a'), g.lit(1)))

g.harness()