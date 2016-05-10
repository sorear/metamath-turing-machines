"""Turing machine for conjecturing that all squares are less than 5."""
import dsl
g = dsl.DSL()

for f in g.defun('incr', ('x',)):
    f.set('x', g.add(g.read('x'), g.lit(1)))

for f in g.defun('square', ('x','y')):
    f.set('y', g.mul(g.read('x'), g.read('x')))

for m in g.main():
    for w in m.whileloop(g.less(g.read('b'), g.lit(5))):
        w.call('square', ('a','b'))
        w.call('incr', ('a',))

g.harness()