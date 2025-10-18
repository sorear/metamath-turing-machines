import pyparsing as pp
import nqlast as nql

def _grammar():

    # "tokens"

    integer_ = pp.Word(pp.nums).setName('integer').setParseAction(lambda t: int(t[0]))
    reserved_words = {'while', 'proc', 'global', 'if', 'return', 'else', 'elsif', 'switch',
                      'case', 'break', 'default', 'true', 'false', 'decz'}
    identifier_ = pp.Word(pp.alphas, pp.alphanums + '_') \
        .addCondition((lambda t: t[0] not in reserved_words), \
            message='reserved word').setName('identifier')

    if_ = pp.Keyword('if')
    else_ = pp.Keyword('else')
    elsif_ = pp.Keyword('elsif')
    while_ = pp.Keyword('while')
    proc_ = pp.Keyword('proc')
    global_ = pp.Keyword('global')
    return_ = pp.Keyword('return')
    switch_ = pp.Keyword('switch')
    case_ = pp.Keyword('case')
    default_ = pp.Keyword('default')
    break_ = pp.Keyword('break')
    true_ = pp.Keyword('true')
    false_ = pp.Keyword('false')
    decz_ = pp.Keyword('decz')
    lt_ = pp.Literal('<') + ~pp.Literal('=')
    gt_ = pp.Literal('>') + ~pp.Literal('=')
    le_ = pp.Literal('<=')
    ge_ = pp.Literal('>=')
    eq_ = pp.Literal('==')
    ne_ = pp.Literal('!=')
    not_ = pp.Literal('!') + ~pp.Literal('=')
    and_ = pp.Literal('&&')
    or_ = pp.Literal('||')
    times_ = pp.Literal('*')
    div_ = pp.Literal('/')
    monus_ = pp.Literal('-')
    equal_ = pp.Literal('=') + ~pp.Literal('=')
    plus_ = pp.Literal('+')
    semi_ = pp.Literal(';')
    colon_ = pp.Suppress(':')
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
    pri_true = true_().setParseAction(lambda t: nql.TrueConst())
    pri_false = false_().setParseAction(lambda t: nql.FalseConst())
    pri_paren = (lpar_ + expr + rpar_)
    pri_expr = pri_int | pri_true | pri_false | pri_reg | pri_paren

    def callop(op, line, *children):
        if isinstance(op, type):
            return op(lineno=line, children=list(children))
        else:
            return op(line, *children)

    def binop_level(prev, assoc, name, op_list):
        def dobinop(line,lhs,op,rhs):
            return callop(op, line, lhs, rhs)
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
                    t[-3:] = [dobinop(line, *t[-3:])]
                else:
                    assert not "unhandled associativity"
            return t[0]
        return (prev + pp.ZeroOrMore(op_list + prev)).setParseAction(associate).setName(name)

    def prefix_level(prev, name, op_list):
        def associate(s, l, t):
            t = list(t)
            while len(t) > 1:
                t[-2:] = [callop(t[-2], pp.lineno(l, s), t[-1])]
            return t[0]
        return (pp.ZeroOrMore(op_list) + prev).setParseAction(associate).setName(name)

    mul_multiply = times_().setParseAction(lambda t: nql.Mul)
    mul_div = div_().setParseAction(lambda t: nql.Div)
    mul_expr = binop_level(pri_expr, 'left', 'multiplicative expression', mul_multiply ^ mul_div)

    add_add = plus_().setParseAction(lambda t: nql.Add)
    add_monus = monus_().setParseAction(lambda t: nql.Monus)
    add_expr = binop_level(mul_expr, 'left', 'additive expression', add_add ^ add_monus)

    rel_less = lt_().setParseAction(lambda t: nql.Less)
    rel_greater = gt_().setParseAction(lambda t: nql.Greater)
    rel_lessequal = le_().setParseAction(lambda t: nql.LessEqual)
    rel_greaterequal = ge_().setParseAction(lambda t: nql.GreaterEqual)
    rel_equal = eq_().setParseAction(lambda t: nql.Equal)
    rel_notequal = ne_().setParseAction(lambda t: nql.NotEqual)
    rel_expr = binop_level(add_expr, 'none', 'relational expression', rel_less ^ rel_greater ^ rel_lessequal ^ rel_greaterequal ^ rel_equal ^ rel_notequal)

    and_and = and_().setParseAction(lambda t: nql.And)
    and_expr = binop_level(rel_expr, 'left', 'and', and_and)

    or_or = or_().setParseAction(lambda t: nql.Or)
    or_expr = binop_level(and_expr, 'left', 'or', or_or)

    not_not = not_().setParseAction(lambda t: nql.Not)
    not_decz = decz_().setParseAction(lambda t: nql.DecZ)
    not_expr = prefix_level(or_expr, 'not expression', not_not ^ not_decz)

    expr << not_expr

    # statement grammar

    stmt = pp.Forward()
    block = (lbra_ + pp.ZeroOrMore(stmt) + rbra_).setParseAction(a(lambda l,t: nql.Block(lineno=l, children=list(t))))

    st_whileloop = (while_ - lpar_ - expr - rpar_ - block).setParseAction(a(lambda l,t: nql.WhileLoop(lineno=l, children=[t[1],t[2]])))

    else_chain = pp.Forward()
    else_none = pp.Empty().setParseAction(lambda t: nql.Block())
    else_else = (else_ - block).setParseAction(lambda t: t[1])
    else_elsif = (elsif_ - lpar_ - expr - rpar_ - block - else_chain).setParseAction(a(lambda l,t: nql.IfThen(lineno=l, children=[t[1],t[2],t[3]])))
    else_chain << (else_else ^ else_elsif ^ else_none)

    st_if = (if_ - lpar_ - expr - rpar_ - block - else_chain).setParseAction(a(lambda l,t: nql.IfThen(lineno=l, children=[t[1], t[2], t[3]])))

    st_assignment = (identifier_ + equal_ + expr + semi_).setParseAction(a(lambda l,t: nql.Assign(lineno=l, children=[nql.Reg(lineno=l, name=t[0]), t[2]])))
    arglist = (lpar_ + pp.Optional(pp.delimitedList(identifier_)) + rpar_).setParseAction(lambda t: [list(t)])
    st_proccall = (identifier_ + arglist + semi_).setParseAction(a(lambda l,t: nql.Call(lineno=l, func=t[0], children=[nql.Reg(lineno=l, name=arg) for arg in t[1]])))
    st_return = (return_ + semi_).setParseAction(a(lambda l,t: nql.Return(lineno=l)))
    st_break = (break_ + semi_).setParseAction(a(lambda l,t: nql.Break(lineno=l)))

    case_arm = (case_ - integer_ - colon_ - pp.ZeroOrMore(stmt)).setParseAction(a(lambda l,t: nql.SwitchArm(lineno=l, case=t[1], children=list(t)[2:])))
    def_arm = (default_ - colon_ - pp.ZeroOrMore(stmt)).setParseAction(a(lambda l,t: nql.SwitchArm(lineno=l, case=None, children=list(t)[1:])))

    st_switch = (switch_ - lpar_ - expr - rpar_ - lbra_ - pp.ZeroOrMore(case_arm | def_arm) - rbra_) \
        .setParseAction(a(lambda l,t: nql.Switch(lineno=l, children=list(t)[1:])))

    stmt << (st_whileloop | st_if | st_switch | st_assignment | st_return | st_break | st_proccall | block)

    # top level

    procdef = (proc_ - identifier_ - arglist - block).setParseAction(a(lambda l,t: nql.ProcDef(lineno=l, name=t[1], parameters=t[2], children=[t[3]])))
    globaldef = (global_ - identifier_ - semi_).setParseAction(a(lambda l,t: nql.GlobalReg(lineno=l, name=t[1])))
    decl = procdef | globaldef

    program = pp.ZeroOrMore(decl).setParseAction(a(lambda l,t: nql.Program(lineno=l, children=list(t))))
    program.ignore(pp.cStyleComment)
    program.enablePackrat()
    return program

grammar = _grammar()
