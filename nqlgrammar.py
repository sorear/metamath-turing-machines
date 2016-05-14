import pyparsing as pp
import nqlast as nql

def _grammar():

    # "tokens"

    integer_ = pp.Word(pp.nums).setName('integer').setParseAction(lambda t: int(t[0]))
    reserved_words = {'while', 'proc', 'global'}
    identifier_ = pp.Word(pp.alphas, pp.alphanums + '_') \
        .addCondition((lambda t: t[0] not in reserved_words), \
            message='reserved word').setName('identifier')

    while_ = pp.Keyword('while')
    proc_ = pp.Keyword('proc')
    global_ = pp.Keyword('global')
    lt_ = pp.Literal('<') + ~pp.Literal('=')
    times_ = pp.Literal('*')
    monus_ = pp.Literal('-')
    equal_ = pp.Literal('=') + ~pp.Literal('=')
    plus_ = pp.Literal('+')
    semi_ = pp.Literal(';')
    lpar_ = pp.Suppress('(')
    rpar_ = pp.Suppress(')')
    lbra_ = pp.Suppress('{')
    rbra_ = pp.Suppress('}')

    expr = pp.Forward()

    # expression grammar

    def a(action):
        def wrapper(s,l,t):
            # print(t)
            return action(pp.lineno(l,s), t)
        return wrapper

    pri_int = integer_().setParseAction(a(lambda l,t: nql.Lit(lineno=l, value=int(t[0]))))
    pri_reg = identifier_().setParseAction(a(lambda l,t: nql.Reg(lineno=l, name=t[0])))
    pri_paren = (lpar_ + expr + rpar_)
    pri_expr = pri_int | pri_reg | pri_paren

    def binop_level(prev, assoc, name, op_list):
        def dobinop(line,lhs,op,rhs):
            if isinstance(op, type):
                return op(lineno=line, children=[lhs, rhs])
            else:
                return op()
        def associate(s,l,t):
            t = list(t)
            line = pp.lineno(l, s)
            while len(t) > 1:
                if assoc == 'none':
                    if len(t) != 3:
                        raise pp.ParseException(s, l, name+' is not associative')
                    t[0:3] = [dobinop(line, *t[0:3])]
                elif assoc == 'left':
                    t[0:3] = [dobinop(line, *t[0:3])]
                elif assoc == 'right':
                    t[-4:-1] = [dobinop(line, *t[-4:-1])]
                else:
                    assert not "unhandled associativity"
            return t[0]
        return (prev + pp.ZeroOrMore(op_list + prev)).setParseAction(associate).setName(name)

    mul_multiply = times_().setParseAction(lambda t: nql.Mul)
    mul_expr = binop_level(pri_expr, 'left', 'multiplicative expression', mul_multiply)

    add_add = plus_().setParseAction(lambda t: nql.Add)
    add_monus = monus_().setParseAction(lambda t: nql.Monus)
    add_expr = binop_level(mul_expr, 'left', 'additive expression', add_add ^ add_monus)

    rel_less = lt_().setParseAction(lambda t: nql.Less)
    rel_expr = binop_level(add_expr, 'none', 'relational expression', rel_less)

    expr << rel_expr

    # statement grammar

    block = pp.Forward()

    whileloop = (while_ + lpar_ + expr + rpar_ + block).setParseAction(a(lambda l,t: nql.WhileLoop(lineno=l, children=[t[1],t[2]])))
    assignment = (identifier_ + equal_ + expr + semi_).setParseAction(a(lambda l,t: nql.Assign(lineno=l, children=[nql.Reg(lineno=l, name=t[0]), t[2]])))
    arglist = (lpar_ + pp.Optional(pp.delimitedList(identifier_)) + rpar_).setParseAction(lambda t: [list(t)])
    proccall = (identifier_ + arglist + semi_).setParseAction(a(lambda l,t: nql.Call(lineno=l, func=t[0], children=[nql.Reg(lineno=l, name=arg) for arg in t[1]])))
    stmt = whileloop | assignment | proccall | block

    block << (lbra_ + pp.ZeroOrMore(stmt) + rbra_).setParseAction(a(lambda l,t: nql.Block(lineno=l, children=list(t))))

    # top level

    procdef = (proc_ - identifier_ - arglist - block).setParseAction(a(lambda l,t: nql.ProcDef(lineno=l, name=t[1], parameters=t[2], children=[t[3]])))
    globaldef = (global_ - identifier_ - semi_).setParseAction(a(lambda l,t: nql.GlobalReg(lineno=l, name=t[1])))
    decl = procdef | globaldef

    program = pp.ZeroOrMore(decl).setParseAction(a(lambda l,t: nql.Program(lineno=l, children=list(t))))
    program.ignore(pp.cStyleComment)
    return program

grammar = _grammar()