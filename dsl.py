"""Implements an EDSL for constructing Turing machines without subclassing
MachineBuilder."""

from framework import Machine, MachineBuilder, Goto, Label, memo

class _Nexpr:
    """Base class for expressions which result in natural numbers.

    Sub classes should define an emit method which generates code to put the
    evaluation result in an initially zero scratch register.

    TODO: context-sensitive code generation and peephole optimization will
    reduce the state count here quite a bit."""

    def emit_nat(self, state):
        raise NotImplementedError()

class _Nread(_Nexpr):
    def __init__(self, reg):
        self._reg = reg

    def emit_nat(self, state):
        ret = state.get_temp()
        save = state.get_temp()
        reg = state.resolve(self._reg)
        state.emit_transfer(reg, ret, save)
        state.emit_transfer(save, reg)
        state.put_temp(save)
        return ret

class _Nop(_Nexpr):
    def __init__(self, *args):
        self._args = args
    def emit_nat(self, state):
        temps = [arg.emit_nat(state) for arg in self._args]
        ret = self.operate(state, *temps)
        for temp in temps:
            state.put_temp(temp)
        return ret

class _Nmul(_Nop):
    def operate(self, state, lhs, rhs):
        save = state.get_temp()
        out = state.get_temp()
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
        return out

class _Nadd(_Nop):
    def operate(self, state, lhs, rhs):
        out = state.get_temp()
        state.emit_transfer(lhs, out)
        state.emit_transfer(rhs, out)
        return out

class _Nlit(_Nexpr):
    def __init__(self, value):
        self._value = value

    def emit_nat(self, state):
        ret = state.get_temp()
        for _ in range(self._value):
            state.emit_inc(ret)
        return ret

class _Bexpr:
    """Base class for expressions which result in booleans."""

    def emit_test(self, state, label, invert=False):
        raise NotImplementedError()

class _Bless(_Bexpr):
    def __init__(self, lhs, rhs):
        self._lhs = lhs
        self._rhs = rhs

    def emit_test(self, state, label, invert=False):
        lhs = self._lhs.emit_nat(state)
        rhs = self._rhs.emit_nat(state)
        monus = state.gensym()
        not_less = state.gensym()
        is_less = state.gensym()
        state.emit_label(monus)
        state.emit_dec(rhs)
        state.emit_goto(not_less)
        state.emit_dec(lhs)
        state.emit_goto(is_less)
        state.emit_goto(monus)
        if invert:
            state.emit_label(not_less)
            state.emit_transfer(lhs)
            state.emit_goto(label)
            state.emit_label(is_less)
            state.emit_transfer(rhs)
        else:
            state.emit_label(is_less)
            state.emit_transfer(rhs)
            state.emit_goto(label)
            state.emit_label(not_less)
            state.emit_transfer(lhs)
        state.put_temp(lhs)
        state.put_temp(rhs)

class _Vexpr:
    """Base class for expressions which return no value."""

    def emit_stmt(self, state):
        raise NotImplementedError()

class _Vset:
    # TODO: augmented additions and subtractions can be peepholed to remove the temporary
    # TODO: when assigning something that doesn't use the old value, it can be constructed in place
    def __init__(self, reg, expr):
        self.reg = reg
        self.expr = expr

    def emit_stmt(self, state):
        temp = self.expr.emit_nat(state)
        state.emit_transfer(state.resolve(self.reg))
        state.emit_transfer(temp, state.resolve(self.reg))
        state.put_temp(temp)

class _Vwhile:
    def __init__(self, expr, block):
        self._expr = expr
        self._block = block

    def emit_stmt(self, state):
        exit = state.gensym()
        again = state.gensym()
        state.emit_label(again)
        self._expr.emit_test(state, exit, invert=True)
        for st in self._block:
            st.emit_stmt(state)
        state.emit_goto(again)
        state.emit_label(exit)

class _Vcall:
    def __init__(self, func, args):
        self._func = func
        self._args = args

    def emit_stmt(self, state):
        state.emit_call(self._func, [state.resolve(arg) for arg in self._args])

class _BlockDef:
    def __init__(self):
        self._block = []

    def whileloop(self, expr):
        block = _BlockDef()
        yield block
        self._block.append(_Vwhile(expr, block._block))

    def set(self, lhs, rhs):
        self._block.append(_Vset(lhs, rhs))

    def call(self, func, args):
        self._block.append(_Vcall(func, args))

class _SubDef(_BlockDef):
    """Stores a subprogram definition at a high level."""
    def __init__(self, name, args):
        self._name = name
        self._args = args
        _BlockDef.__init__(self)

class _SubEmitter:
    """Tracks state while lowering a _SubDef to a call sequence."""

    def __init__(self, register_map, machine_builder):
        self._register_map = register_map
        self._machine_builder = machine_builder
        self._scratch_next = 0
        self._scratch_free = []
        self._output = []

    def emit_transfer(self, *regs):
        self._output.append(self._machine_builder.transfer(*regs))

    def emit_label(self, label):
        self._output.append(Label(label))

    def emit_goto(self, label):
        self._output.append(Goto(label))

    def emit_inc(self, reg):
        self._output.append(reg.inc)

    def emit_dec(self, reg):
        self._output.append(reg.dec)

    def emit_call(self, func_name, args):
        func = self._machine_builder.instantiate(func_name, tuple(arg.name for arg in args))
        self._output.append(func)

    def resolve(self, regname):
        reg = self._register_map.get(regname) or '_G' + regname
        return self._machine_builder.register(reg) if isinstance(reg,str) else reg

    def put_temp(self, reg):
        self._scratch_free.append(reg)

    def get_temp(self):
        if self._scratch_free:
            return self._scratch_free.pop()
        self._scratch_next += 1
        return self._machine_builder.register('_scratch_' + str(self._scratch_next))

    def gensym(self):
        self._machine_builder._gensym += 1
        return 'gen' + str(self._machine_builder._gensym)

class _AstMachine(MachineBuilder):
    def __init__(self, ast):
        super().__init__()
        self._ast = ast
        self._fun_instances = {}
        self._gensym = 0

    @memo
    def instantiate(self, name, args):
        defn = self._ast._defuns[name]
        emit = _SubEmitter(dict(zip(defn._args, args)), self)
        for s in defn._block:
            s.emit_stmt(emit)
        return self.makesub(name=name + '(' + ','.join(args) + ')', *emit._output)

    def main(self):
        return self.instantiate('main', ())

class DSL:
    def __init__(self):
        self._defuns = {}

    def defun(self, name, args):
        assert name not in self._defuns
        self._defuns[name] = _SubDef(name, args)
        yield self._defuns[name]

    def main(self):
        return self.defun('main', ())

    def lit(self, value):
        return _Nlit(value)

    def read(self, reg):
        return _Nread(reg)

    def less(self, lhs, rhs):
        return _Bless(lhs, rhs)

    def mul(self, lhs, rhs):
        return _Nmul(lhs, rhs)

    def add(self, lhs, rhs):
        return _Nadd(lhs, rhs)

    def harness(self):
        mach1 = _AstMachine(self)
        mach1.pc_bits = 50
        order = mach1.main().order
        mach2 = _AstMachine(self)
        mach2.pc_bits = order
        Machine(mach2).harness()
