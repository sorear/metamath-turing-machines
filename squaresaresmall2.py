"""Turing machine for conjecturing that all squares are less than 5."""
import nqlast as l

ast = l.Program(children=[
    l.GlobalReg(name='a'),
    l.GlobalReg(name='b'),
    l.ProcDef(name='incr', parameters=('x',), children=[
        l.Block(children=[
            l.Assign(children=[l.Reg(name='x'), l.Add(children=[l.Reg(name='x'), l.Lit(value=1)])]),
        ]),
    ]),
    l.ProcDef(name='square', parameters=['x', 'y'], children=[
        l.Block(children=[
            l.Assign(children=[l.Reg(name='y'),
                               l.Mul(children=[l.Reg(name='x'), l.Reg(name='x')])]),
        ]),
    ]),
    l.ProcDef(name='main', parameters=[], children=[
        l.Block(children=[
            l.WhileLoop(children=[
                l.Less(children=[l.Reg(name='b'), l.Lit(value=5)]),
                l.Block(children=[
                    l.Call(func='square', children=[l.Reg(name='a'), l.Reg(name='b')]),
                    l.Call(func='incr', children=[l.Reg(name='a')])
                ])
            ])
        ])
    ])
])

l.harness(ast)
