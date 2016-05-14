"""Implements an EDSL for constructing Turing machines without subclassing
MachineBuilder."""

from framework import Machine, MachineBuilder, Goto, Label, memo

class Node:
    """Base class for all Not Quite Laconic syntax nodes."""
    def __init__(self, **kwargs):
        self.lineno = kwargs.pop('lineno', 0)
        self.children = kwargs.pop('children', [])
        assert not kwargs
        self.check_children()

    child_types = ()

    def check_children(self):
        """Verifies that the node has the correct number and types of child
        nodes."""
        if isinstance(self.child_types, tuple):
            assert len(self.children) == len(self.child_types)
            for child, ctype in zip(self.children, self.child_types):
                assert isinstance(child, ctype)
        else:
            for child in self.children:
                assert isinstance(child, self.child_types)

    def error(self, message):
        """Print an error using the line number of this node."""
        raise str(self.lineno) + ": " + message

    repr_suppress = ('lineno','children')

    def __repr__(self):
        result = []
        result.append(self.__class__.__name__ + '(')
        result.append(('\n  ',''))

        has_items = False
        for k, v in vars(self).items():
            if k in self.repr_suppress:
                continue
            result.append(k + '=' + repr(v).replace('\n', '\n  '))
            result.append((',\n  ', ', '))
            has_items = True

        if self.children:
            result.append('children=[')
            result.append(('\n    ', ''))
            for child in self.children:
                result.append(repr(child).replace('\n', '\n    '))
                result.append((',\n    ', ', '))
            result.pop()
            result.append(']')
        elif has_items:
            result.pop()
        result.append(')')

        result = [(tup if isinstance(tup, tuple) else (tup, tup)) for tup in result]
        broken = ''.join(a for a, b in result)
        unbroken = ''.join(b for a, b in result)
        if len(unbroken) < 80 and '\n' not in unbroken:
            return unbroken
        else:
            return broken

class NatExpr(Node):
    """Base class for expressions which result in a natural number.

    Sub classes should define an emit method which generates code to put the
    evaluation result in a caller-allocated temporary register.

    TODO: context-sensitive code generation and peephole optimization will
    reduce the state count here quite a bit."""

    def emit_nat(self, state, target):
        """Calculate the value of this expression into the target register,
        which is guaranteed to be zero by the caller unless is_additive
        returns True."""
        temps = []
        for child in self.children:
            temp = state.get_temp()
            temps.append(temp)
            child.emit_nat(state, temp)
        self.emit_nat_op(state, target, temps)
        for temp in temps:
            state.put_temp(temp)

    def emit_nat_op(self, state, target, temps):
        """Calculate the value of this expression with the arguments already
        evaluated.

        To customize argument evaluation, override emit_nat instead."""
        raise NotImplementedError()

    def is_additive(self):
        """Returns True if emit_nat actually just adds and is safe for non-zero targets."""
        return False

class Reg(NatExpr):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        super().__init__(**kwargs)

    def is_additive(self):
        return True

    def emit_nat_op(self, state, target, _args):
        save = state.get_temp()
        reg = state.resolve(self.name)
        state.emit_transfer(reg, target, save)
        state.emit_transfer(save, reg)
        state.put_temp(save)

class Mul(NatExpr):
    child_types = (NatExpr, NatExpr)
    def is_additive(self):
        return True

    def emit_nat_op(self, state, out, args):
        lhs, rhs = args
        save = state.get_temp()
        again = state.gensym()
        done = state.gensym()
        state.emit_label(again)
        state.emit_dec(lhs)
        state.emit_goto(done)
        state.emit_transfer(rhs, save, out)
        state.emit_transfer(save, rhs)
        state.emit_goto(again)
        state.emit_label(done)
        state.emit_transfer(rhs)
        state.put_temp(save)

class Div(NatExpr):
    child_types = (NatExpr, NatExpr)
    def is_additive(self):
        return True

    def emit_nat(self, state, out):
        dividend_ex, divisor_ex = self.children

        dividend = state.get_temp()
        divisor = state.get_temp()

        loop_quotient = state.gensym()
        loop_divisor = state.gensym()
        exhausted = state.gensym()
        full_divisor = state.gensym()

        dividend_ex.emit_nat(state, dividend)

        state.emit_label(loop_quotient)
        divisor_ex.emit_nat(state, divisor)
        state.emit_label(loop_divisor)
        state.emit_dec(divisor)
        state.emit_goto(full_divisor)
        state.emit_dec(dividend)
        state.emit_goto(exhausted)
        state.emit_goto(loop_divisor)
        state.emit_label(full_divisor)

        state.emit_inc(out)
        state.emit_goto(loop_quotient)
        state.emit_label(exhausted)
        state.emit_transfer(divisor)

        state.put_temp(dividend)
        state.put_temp(divisor)

class Add(NatExpr):
    child_types = NatExpr
    def is_additive(self):
        return True

    def emit_nat_op(self, state, out, args):
        # TODO: we don't need temps for the additive children
        for arg in args:
            state.emit_transfer(arg, out)

class Lit(NatExpr):
    def __init__(self, **kwargs):
        self.value = kwargs.pop('value')
        super().__init__(**kwargs)

    def is_additive(self):
        return True

    def emit_nat_op(self, state, out, _args):
        for _ in range(self.value):
            state.emit_inc(out)

class Monus(NatExpr):
    """Subtracts the right argument from the left argument, clamping to zero
    (also known as the "monus" operator)."""
    child_types = (NatExpr, NatExpr)

    def emit_nat_op(self, state, out, args):
        lhs, rhs = args
        # TODO: forward directly out to lhs
        state.emit_transfer(lhs, out)
        loop = state.gensym()
        done = state.gensym()
        state.emit_label(loop)
        state.emit_dec(rhs)
        state.emit_goto(done)
        state.emit_dec(out)
        state.emit_noop()
        state.emit_goto(loop)
        state.emit_label(done)

class BoolExpr(Node):
    """Base class for expressions which result in a boolean test."""

    def emit_test(self, state, target, invert):
        """Evaluate the test and jump to label if the test is true, subject to
        the inversion flag."""
        temps = []
        for child in self.children:
            temp = state.get_temp()
            temps.append(temp)
            child.emit_nat(state, temp)
        self.emit_test_op(state, target, invert, temps)
        for temp in temps:
            state.put_temp(temp)

    def emit_test_op(self, state, target, invert, temps):
        """Calculate the value of this test with the arguments already
        evaluated.

        To customize argument evaluation, override emit_test instead."""
        raise NotImplementedError()

class CompareBase(BoolExpr):
    child_types = (NatExpr, NatExpr)
    jump_lt = False
    jump_eq = False
    jump_gt = False

    def emit_test_op(self, state, label, invert, temps):
        lhs, rhs = temps

        monus = state.gensym()
        not_less = state.gensym()
        is_less = state.gensym()
        no_jump = state.gensym()

        state.emit_label(monus)
        state.emit_dec(rhs)
        state.emit_goto(not_less)
        state.emit_dec(lhs)
        state.emit_goto(is_less)
        state.emit_goto(monus)

        state.emit_label(not_less)
        if self.jump_eq != self.jump_gt:
            state.emit_dec(lhs)
            state.emit_goto(label if self.jump_eq ^ invert else no_jump)
        state.emit_transfer(lhs)
        state.emit_goto(label if self.jump_gt ^ invert else no_jump)

        state.emit_label(is_less)
        state.emit_transfer(rhs)
        state.emit_goto(label if self.jump_lt ^ invert else no_jump)

        state.emit_label(no_jump)

class Less(CompareBase):
    jump_lt = True

class LessEqual(CompareBase):
    jump_lt = True
    jump_eq = True

class Greater(CompareBase):
    jump_gt = True

class GreaterEqual(CompareBase):
    jump_eq = True
    jump_gt = True

class Equal(CompareBase):
    jump_eq = True

class NotEqual(CompareBase):
    jump_lt = True
    jump_gt = True

class Not(BoolExpr):
    child_types = (BoolExpr,)

    def emit_test(self, state, label, invert):
        self.children[0].emit_test(state, label, not invert)

class VoidExpr(Node):
    """Base class for expressions which return no value."""

    def emit_stmt(self, state):
        raise NotImplementedError()

class Assign(VoidExpr):
    child_types = (Reg, NatExpr)
    # TODO: augmented additions and subtractions can be peepholed to remove the temporary
    # TODO: when assigning something that doesn't use the old value, it can be constructed in place

    def emit_stmt(self, state):
        temp = state.get_temp()
        lhs, rhs = self.children
        rhs.emit_nat(state, temp)
        state.emit_transfer(state.resolve(lhs.name))
        state.emit_transfer(temp, state.resolve(lhs.name))
        state.put_temp(temp)

class Block(VoidExpr):
    child_types = VoidExpr
    def emit_stmt(self, state):
        for st in self.children:
            st.emit_stmt(state)

class WhileLoop(VoidExpr):
    child_types = (BoolExpr, VoidExpr)
    def emit_stmt(self, state):
        test, block = self.children
        exit = state.gensym()
        again = state.gensym()
        state.emit_label(again)
        test.emit_test(state, exit, True)
        block.emit_stmt(state)
        state.emit_goto(again)
        state.emit_label(exit)

class IfThen(VoidExpr):
    child_types = (BoolExpr, VoidExpr, VoidExpr)
    def emit_stmt(self, state):
        test, then_, else_ = self.children
        l_else = state.gensym()
        l_then = state.gensym()
        test.emit_test(state, l_else, True)
        then_.emit_stmt(state)
        state.emit_goto(l_then)
        state.emit_label(l_else)
        else_.emit_stmt(state)
        state.emit_label(l_then)

class Call(VoidExpr):
    child_types = Reg
    def __init__(self, **kwargs):
        self.func = kwargs.pop('func')
        super().__init__(**kwargs)

    def emit_stmt(self, state):
        state.emit_call(self.func, [state.resolve(arg.name) for arg in self.children])

class Return(VoidExpr):
    def emit_stmt(self, state):
        state.emit_return()

class GlobalNode(Node):
    pass

class ProcDef(GlobalNode):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.parameters = kwargs.pop('parameters')
        super().__init__(**kwargs)

    child_types = (VoidExpr,)

class GlobalReg(GlobalNode):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        super().__init__(**kwargs)

class Program(Node):
    child_types = GlobalNode
    repr_suppress = Node.repr_suppress + ('by_name',)
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.by_name = {node.name: node for node in self.children}

class SubEmitter:
    """Tracks state while lowering a _SubDef to a call sequence."""

    def __init__(self, register_map, machine_builder):
        self._register_map = register_map
        self._machine_builder = machine_builder
        self._scratch_next = 0
        self._scratch_used = []
        self._scratch_free = []
        self._output = []
        self._return_label = None

    def emit_transfer(self, *regs):
        self._output.append(self._machine_builder.transfer(*regs))

    def emit_halt(self):
        self._output.append(self._machine_builder.halt())

    def emit_noop(self):
        self._output.append(self._machine_builder.noop(0))

    def emit_label(self, label):
        self._output.append(Label(label))

    def emit_goto(self, label):
        self._output.append(Goto(label))

    def emit_return(self):
        if not self._return_label:
            self._return_label = self.gensym()
        self.emit_goto(self._return_label)

    def close_return(self):
        if self._return_label:
            self.emit_label(self._return_label)

    def emit_inc(self, reg):
        self._output.append(reg.inc)

    def emit_dec(self, reg):
        self._output.append(reg.dec)

    def emit_call(self, func_name, args):
        assert len(self._scratch_used) == 0
        func = self._machine_builder.instantiate(func_name, tuple(arg.name for arg in args))
        self._output.append(func)

    def resolve(self, regname):
        reg = self._register_map.get(regname) or '_G' + regname
        return self._machine_builder.register(reg) if isinstance(reg,str) else reg

    def put_temp(self, reg):
        self._scratch_used.remove(reg)
        self._scratch_free.append(reg)

    def get_temp(self):
        if self._scratch_free:
            var = self._scratch_free.pop()
        else:
            self._scratch_next += 1
            var = self._machine_builder.register('_scratch_' + str(self._scratch_next))
        self._scratch_used.append(var)
        return var

    def gensym(self):
        self._machine_builder._gensym += 1
        return 'gen' + str(self._machine_builder._gensym)

class AstMachine(MachineBuilder):
    def __init__(self, ast):
        super().__init__()
        self._ast = ast
        self._fun_instances = {}
        self._gensym = 0

    @memo
    def instantiate(self, name, args):
        defn = self._ast.by_name[name]
        assert isinstance(defn, ProcDef)
        emit = SubEmitter(dict(zip(defn.parameters, args)), self)
        defn.children[0].emit_stmt(emit)
        emit.close_return()
        if name == 'main':
            emit.emit_halt()
        return self.makesub(name=name + '(' + ','.join(args) + ')', *emit._output)

    def main(self):
        return self.instantiate('main', ())

def harness(ast, args=None):
    mach1 = AstMachine(ast)
    mach1.pc_bits = 50
    order = mach1.main().order
    mach2 = AstMachine(ast)
    mach2.pc_bits = order
    Machine(mach2).harness(args)
