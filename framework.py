"""Framework for building Turing machines using a register machine abstraction
and binary decision diagrams in place of subprograms."""
# Tape layout: PC:bit[NNN] 0 0 ( 1 1* 0 )*
#
# each thing after the PC is a unary register.
#
# There is a "dispatch" state which assumes the head is at position zero, and
# reads PC bits through a decision tree to find out what to do.
#
# The decision tree has shared subtrees - this is how we handle "subroutines".
# Naturally these shared subtrees have to handle different "contexts".
#
# we shift 1 left of the PC MSB during carry phases; the initial state is the
# leftmost shift state, so the total shift is always non-negative.

from collections import namedtuple
import argparse

class Halt:
    """Special machine state which halts the Turing machine."""
    def __init__(self):
        self.name = 'HALT'

class State:
    """Represents a Turing machine state.

    Instances of State can be initialized either at construction or using
    the be() method; the latter allows for cyclic graphs to be defined."""
    def __init__(self, **kwargs):
        self.set = False
        self.name = '**UNINITIALIZED**'
        if kwargs:
            self.be(**kwargs)

    def be(self, name, move=None, next=None, write=None,
           move0=None, next0=None, write0=None,
           move1=None, next1=None, write1=None):
        """Defines a Turing machine state.

        The movement direction, next state, and new tape value can be defined
        depending on the old tape value, or for both tape values at the same time.
        Next state and direction must be provided, tape value can be omitted for no change."""
        assert not self.set
        self.set = True
        self.name = name
        self.move0 = move0 or move
        self.move1 = move1 or move
        self.next0 = next0 or next
        self.next1 = next1 or next
        self.write0 = write0 or write or '0'
        self.write1 = write1 or write or '1'
        assert self.move0 in (-1, 1)
        assert self.move1 in (-1, 1)
        assert self.write0 in ('0', '1')
        assert self.write1 in ('0', '1')
        assert isinstance(self.name, str)
        assert isinstance(self.next0, State) or isinstance(self.next0, Halt)
        assert isinstance(self.next1, State) or isinstance(self.next1, Halt)

    def clone(self, other):
        """Makes this state equivalent to another state, which must already be initialized."""
        assert isinstance(other, State) and other.set
        self.be(name=other.name, move0=other.move0, next0=other.next0,
                write0=other.write0, move1=other.move1, next1=other.next1,
                write1=other.write1)

def make_bits(num, bits):
    """Constructs a bit string of length=bits for an integer num."""
    assert num < (1 << bits)
    if bits == 0:
        return ''
    return '{num:0{bits}b}'.format(num=num, bits=bits)

def memo(func):
    """Decorator which memoizes a method, so it will be called once with a
    given set of arguments."""
    def _wrapper(self, *args):
        key = (func,) + args
        if key not in self._memos:
            self._memos[key] = None
            self._memos[key] = func(self, *args)
        if not self._memos[key]:
            print("recursion detected", func.__name__, repr(args))
            assert False
        return self._memos[key]

    return _wrapper

Label = namedtuple('Label', ['name'])
Label.size = 0
Label.alignment = 1
Label.is_decrement = False
Goto = namedtuple('Goto', ['name'])
Goto.size = 1
Goto.alignment = 1
Goto.is_decrement = False
Register = namedtuple('Register', 'name index inc dec')

class Subroutine:
    """Class wrapping a compiled subprogram, which is an internal node in the
    program BDD.

    A subprogram consumes a power-of-two number of PC values, and can appear
    at any correctly aligned PC; the entry state is entered with the tape head
    on the first bit of the subprogram's owned portion of the PC."""
    def __init__(self, entry, order, name, child_map=None, is_decrement=False):
        self.entry = entry
        self.name = name
        self.order = order
        self.size = 1 << order
        self.alignment = self.size
        self.is_decrement = is_decrement
        self.child_map = child_map or {}

class Align:
    def __init__(self, align):
        self.size = 0
        self.alignment = align

InsnInfo = namedtuple('InsnInfo', 'sub labels goto')

def make_dispatcher(child_map, name, order, at_prefix=''):
    """Constructs one or more dispatch states to route to a child map.

    Each key in the child map must be a binary string no longer than
    the order, and every binary string of length equal to the order must
    have exactly one child map key as a prefix.  The generated states will
    read bits going right and fall into the child states after reading
    exactly the prefix."""
    if at_prefix in child_map:
        return child_map[at_prefix].sub.entry
    assert len(at_prefix) <= order
    switch = State()
    switch.be(move=1, name=name + '[' + at_prefix + ']',
              next0=make_dispatcher(child_map, name, order, at_prefix + '0'),
              next1=make_dispatcher(child_map, name, order, at_prefix + '1'))
    return switch

def cfg_optimizer(parts):
    parts = list(parts)

    # Thread jumps to jumps
    # Delete jumps to the next instruction
    counter = 0
    label_map = {}
    rlabel_map = {}
    goto_map = {}
    labels = []
    for insn in parts:
        if isinstance(insn, Label):
            labels.append(insn.name)
        else:
            for label in labels:
                label_map[label] = counter
                rlabel_map[counter] = label
            labels = []
            if isinstance(insn, Goto):
                goto_map[counter] = insn.name
            counter += 1
    for label in labels:
        label_map[label] = counter
        rlabel_map[counter] = label

    def follow(count):
        for _ in range(10):
            if count not in goto_map:
                break
            count = label_map[goto_map[count]]
        return count
    # print(repr(parts))

    counter = 0
    for index, insn in enumerate(parts):
        if isinstance(insn, Label):
            continue
        if isinstance(insn, Goto):
            direct_goes_to = label_map[goto_map[counter]]
            goes_to = follow(direct_goes_to)
            next_goes_to = goto_map.get(counter+1) and follow(counter+1)

            # print("CFGO", insn.name, counter, goes_to, next_goes_to)
            if goes_to == counter + 1 or goes_to == next_goes_to:
                parts[index] = None
            elif direct_goes_to != goes_to:
                parts[index] = Goto(rlabel_map[goes_to])
        counter += 1

    # print(repr(parts))

    # Delete dead code

    # label_to_index = {}
    # for index, insn in enumerate(parts):
    #     if isinstance(insn, Label):
    #         label_to_index[insn.name] = index

    # grey_index = [0]
    # black_index = set()
    # while grey_index:
    #     ix = grey_index.pop()
    #     if ix in black_index or ix >= len(parts):
    #         continue
    #     black_index.add(ix)

    #     if isinstance(insn, Goto):
    #         grey_index.append(label_to_index[insn.name])
    #     else:
    #         grey_index.append(ix + 1)
    #         if insn and insn.is_decrement:
    #             grey_index.append(ix + 2)

    # for index in range(len(parts)):
    #     if index not in black_index:
    #         print("DEAD CODE")
    #         parts[index] = None

    return tuple(p for p in parts if p)

class MachineBuilder:
    """Subclassable class of utilities for constructing Turing machines using
    BDD-compressed register machines."""
    pc_bits = 0
    quick = 0
    # Quick=0: Print TM
    # Quick=1: Simulate TM, print all steps
    # Quick=2: Simulate TM, print at dispatch
    # Quick=3: Simulate compressed register machine
    # Quick=4: as Quick=3 except subroutines can cheat
    # Quick=5: subroutines can cheat to the extent of storing non-integers

    def __init__(self, control_args):
        self._nextreg = 0
        self._memos = {}
        self.control_args = control_args

    # leaf procs which implement register machine operations
    # on entry to a leaf proc the tape head is just after the PC

    @memo
    def reg_incr(self, index):
        """Primitive subroutine which decrements a register."""
        if index == -2:
            entry = self.register_common().inc
        else:
            entry = State()
            entry.be(move=1, next1=entry, next0=self.reg_incr(index-1), name='reg_incr.'+str(index))

        return entry

    @memo
    def reg_decr(self, index):
        """Primitive subroutine which decrements a register.  The PC will be
        incremented by 2 if successful; if the register was zero, it will be
        unchanged and the PC will be incremented by 1."""
        if index == -2:
            entry = self.register_common().dec
        else:
            entry = State()
            entry.be(move=1, next1=entry, next0=self.reg_decr(index-1), name='reg_decr.'+str(index))

        return entry

    @memo
    def reg_init(self):
        """Primitive subroutine which initializes a register.  Call this N
        times before using registers less than N."""
        return Subroutine(self.register_common().init, 0, 'reg_init')

    @memo
    def register_common(self):
        """Primitive register operations start with the tape head on the first
        1 bit of a register, and exit by running back into the dispatcher."""
        (inc_shift_1, inc_shift_0, dec_init, dec_check, dec_scan_1,
         dec_scan_0, dec_scan_done, dec_shift_0, dec_shift_1, dec_restore,
         return_0, return2_0, return_1, return2_1, init_f1, init_f2,
         init_scan_1, init_scan_0) = (State() for i in range(18))

        # Initialize routine
        init_f1.be(move=1, next=init_f2, name='init.f1')
        init_f2.be(move=1, next=init_scan_0, name='init.f2')
        init_scan_1.be(move=1, next1=init_scan_1, next0=init_scan_0, name='init.scan_1') # only 0 is possible
        init_scan_0.be(write0='1', move0=-1, next0=return_1, move1=1, next1=init_scan_1, name='init.scan_0')

        # Increment the register, the first 1 bit of which is under the tape head
        inc_shift_1.be(move=1, write='1', next0=inc_shift_0, next1=inc_shift_1, name='inc.shift_1')
        inc_shift_0.be(write='0', next0=return_0, move0=-1, next1=inc_shift_1, move1=1, name='inc.shift_0')

        # Decrementing is a bit more complicated, we need to mark the register we're on
        dec_init.be(write='0', move=1, next=dec_check, name='dec.init')
        dec_check.be(move0=-1, next0=dec_restore, move1=1, next1=dec_scan_1, name='dec.check')

        dec_scan_1.be(move=1, next1=dec_scan_1, next0=dec_scan_0, name='dec.scan_1')
        dec_scan_0.be(move1=1, next1=dec_scan_1, move0=-1, next0=dec_scan_done, name='dec.scan_0')
        # scan_done = on 0 after last reg
        dec_scan_done.be(move=-1, next=dec_shift_0, name='dec.scan_done')
        dec_shift_0.be(write='0', move0=-1, next0=return2_0, move1=-1, next1=dec_shift_1, name='dec.shift_0')
        # if shifting 0 onto 0, we're moving the marker we created
        # let it overlap the fence
        dec_shift_1.be(write='1', move=-1, next0=dec_shift_0, next1=dec_shift_1, name='dec.shift_1')

        dec_restore.be(write='1', move=-1, next=return_1, name='dec.restore')

        return_0.be(move=-1, next0=self.nextstate(), next1=return_1, name='return.0')
        return2_0.be(move=-1, next0=self.nextstate_2(), next1=return2_1, name='return2.0')
        return_1.be(move=-1, next0=return_0, next1=return_1, name='return.1')
        return2_1.be(move=-1, next0=return2_0, next1=return2_1, name='return2.1')

        return namedtuple('register_common', 'inc dec init')(inc_shift_1, dec_init, init_f1)

    # Implementing the subroutine model

    @memo
    def dispatchroot(self):
        """A Turing state which issues the correct operation starting from the first PC bit."""
        return State()

    @memo
    def nextstate(self):
        """A Turing state which increments PC by 1, with the tape head on the last PC bit."""
        return self.dispatch_order(0, 1)

    @memo
    def nextstate_2(self):
        """A Turing state which increments PC by 2, with the tape head on the last PC bit."""
        return State(move=-1, next=self.dispatch_order(1, 1), name='nextstate_2')

    @memo
    def dispatch_order(self, order, carry_bit):
        """Constructs Turing states which move from the work area back to the PC head.

        On entry, the head should be order bits left of the rightmost bit of the program
        counter; if carry_bit is set, the bit the head is on will be incremented."""
        if order == self.pc_bits:
            return State(move=+1, next=self.dispatchroot(), name='0')
        assert order < self.pc_bits
        if carry_bit:
            return State(write0='1', next0=self.dispatch_order(order + 1, 0),
                         write1='0', next1=self.dispatch_order(order + 1, 1),
                         move=-1, name='dispatch.{}.carry'.format(order))
        else:
            return State(next=self.dispatch_order(order + 1, 0), move=-1,
                         name='dispatch.{}'.format(order))

    @memo
    def noop(self, order):
        """A subprogram of given size which does nothing.

        Used automatically to maintain alignment."""
        reverse = State(move=-1, next=self.dispatch_order(order, 1), name='noop.{}'.format(order))
        return Subroutine(reverse, order, reverse.name)

    @memo
    def halt(self):
        """A subprogram which halts the Turing machine when your work is done."""
        return Subroutine(Halt(), 0, 'halt')

    @memo
    def jump(self, order, rel_pc, sub_name):
        """A subprogram which replaces a suffix of the PC, for relative jumps.

        Used automatically by the Goto operator."""
        assert rel_pc < (1 << (order + 1))
        steps = [State() for i in range(order + 2)]
        steps[order+1] = self.dispatch_order(order, rel_pc >> order)
        steps[0].be(move=-1, next=steps[1], \
            name='{}.jump({},{},{})'.format(sub_name, rel_pc, order, 0))
        for i in range(order):
            bit = str((rel_pc >> i) & 1)
            steps[i+1].be(move=-1, next=steps[i+2], write=bit, \
                name='{}.jump({},{},{})'.format(sub_name, rel_pc, order, i+1))

        return Subroutine(steps[0], 0, '{}.jump({},{})'.format(sub_name, rel_pc, order))

    @memo
    def rjump(self, rel_pc):
        """A subprogram which adds a constant to the PC, for relative jumps."""
        steps = [(State(), State()) for i in range(self.pc_bits + 1)]
        steps.append(2 * (self.dispatch_order(self.pc_bits, 0),))
        steps[0][0].be(move=-1, next=steps[1][0], name='rjump({})({})'.format(rel_pc, 0))
        for i in range(self.pc_bits):
            bit = (rel_pc >> i) & 1
            steps[i+1][0].be(move=-1, next0=steps[i+2][0], write0=str(bit), \
                next1=steps[i+2][bit], write1=str(1-bit), \
                name='rjump({})({})'.format(rel_pc, i+1))
            steps[i+1][1].be(move=-1, next0=steps[i+2][bit], write0=str(1-bit), \
                next1=steps[i+2][1], write1=str(bit), \
                name='rjump({})({}+)'.format(rel_pc, i+1))

        return Subroutine(steps[0][0], 0, 'rjump({})'.format(rel_pc))

    # TODO: subprogram compilation needs to be substantially lazier in order to do
    # effective inlining and register allocation
    def makesub(self, *parts, name):
        """Assigns PC values within a subprogram and creates the dispatcher."""
        # first find out where everything is and how big I am

        label_offsets = {}
        label_map = {}
        goto_map = {}
        real_parts = []
        offset = 0

        if not self.control_args.no_cfg_optimize:
            parts = cfg_optimizer(parts)

        if name == 'main()':
            # inject code to initialize registers (a bit of a hack)
            regcount = self._nextreg
            while regcount & (regcount - 1):
                regcount += 1
            parts = regcount * (self.reg_init(), ) + parts

        for part in parts:
            if isinstance(part, Label):
                # labels take up no space
                label_offsets[part.name] = offset
                label_map.setdefault(offset, []).append(part.name)
                continue # not a real_part

            if isinstance(part, Goto):
                goto_map[offset] = part.name

            # parts must be aligned
            while offset % part.alignment:
                noop_order = (offset & -offset).bit_length() - 1
                offset += 1 << noop_order
                real_parts.append(self.noop(noop_order))

            if isinstance(part, Align):
                continue

            real_parts.append(part)
            offset += part.size

        assert offset > 0

        order = 0
        while offset > (1 << order):
            order += 1

        # if name == 'main()':
        while offset < (1 << order):
            noop_order = (offset & -offset).bit_length() - 1
            offset += 1 << noop_order
            real_parts.append(self.noop(noop_order))

        offset = 0
        child_map = {}

        jumps_required = set()

        for part in real_parts:
            if isinstance(part, Goto):
                jump_order = 0
                target = label_offsets[part.name]
                while True:
                    base = (offset >> jump_order) << jump_order
                    rel = target - base
                    if rel >= 0 and rel < (1 << (jump_order + 1)):
                        jumps_required.add((jump_order, rel))
                        break
                    jump_order += 1
            offset += part.size
        offset = 0

        for part in real_parts:
            if isinstance(part, Goto):
                assert part.name in label_offsets
                target = label_offsets[part.name]
                if self.control_args.relative_jumps:
                    part = self.rjump(target - offset)
                else:
                    part = None
                    for jump_order in range(order + 1):
                        base = (offset >> jump_order) << jump_order
                        rel = target - base
                        if (jump_order, rel) in jumps_required:
                            part = self.jump(jump_order, rel, name)
                            # don't break, we want to take the largest reqd jump
                            # except for very short jumps, those have low enough
                            # entropy to be worthwhile
                            if jump_order < 3:
                                break
                    assert part
            offset_bits = make_bits(offset >> part.order, order - part.order)
            goto_line = goto_map.get(offset)
            label_line = label_map.get(offset)
            child_map[offset_bits] = InsnInfo(part, label_line, goto_line)
            offset += 1 << part.order

        return Subroutine(make_dispatcher(child_map, name, order), order, name, child_map=child_map)

    # Utilities...
    @memo
    def register(self, name):
        """Assigns a name to a register, and creates the primitive inc/dec routines."""
        index = self._nextreg
        self._nextreg += 1
        pad = 0

        inc = Subroutine(self.reg_incr(index), 0, 'reg_incr('+name+')')
        dec = Subroutine(self.reg_decr(index), 0, 'reg_decr('+name+')', is_decrement=True)

        return Register(name, index, inc, dec)

    def regfile(self, *regs):
        """Assigns names to one or more registers, and creates the primitive inc/dec routines."""
        return [self.register(name) for name in regs]

    @memo
    def transfer(self, source, *to):
        """Subprogram which moves values between registers.

        The source register will be cleared, and its value will be added to each to register."""
        name = 'transfer(' + ','.join([source.name] + [x.name for x in sorted(to)]) + ')'
        return self.makesub(
            Label('again'),
            source.dec,
            Goto('zero'),
            *([tox.inc for tox in sorted(to)] + [
                Goto('again'),
                Label('zero'),
            ]),
            name=name
        )



class Machine:
    """Manipulates and debugs the generated Turing machine for a MachineBuilder."""
    def __init__(self, builder):
        self.builder = builder
        self.main = builder.main()

        if self.main.order != builder.pc_bits:
            print('pc_bits does not match calculated main order:', self.main.order, builder.pc_bits)
            assert False

        self.builder.dispatchroot().clone(self.main.entry)
        self.entry = self.builder.dispatch_order(self.builder.pc_bits, 0)

        self.state = self.entry
        self.left_tape = []
        self.current_tape = '0'
        self.right_tape = []
        self.longest_label = max(len(state.name) for state in self.reachable())

    def harness(self, args):
        """Processes command line arguments and runs the test harness for a machine."""

        if not args.dont_compress:
            self.compress()

        if args.print_subs:
            self.print_subs()

        if args.print_tm:
            self.print_machine()

        if args.run_tm:
            while isinstance(self.state, State):
                self.tm_step()

    def compress(self):
        """Combine pairs of equivalent states in the turing machine."""
        while True:
            did_work = False
            unique_map = {}
            replacement_map = {}

            for state in self.reachable():
                tup = (state.next0, state.next1, state.write0, state.write1,
                       state.move0, state.move1)
                if tup in unique_map:
                    replacement_map[state] = unique_map[tup]
                else:
                    unique_map[tup] = state

            for state in self.reachable():
                if state.next0 in replacement_map:
                    did_work = True
                    state.next0 = replacement_map[state.next0]
                if state.next1 in replacement_map:
                    did_work = True
                    state.next1 = replacement_map[state.next1]

            if self.entry in replacement_map:
                did_work = True
                self.entry = replacement_map[self.entry]

            if not did_work:
                break

    def print_subs(self):
        """Dump the subroutines used by this machine."""

        stack = [self.main]
        utilizations = {}
        while stack:
            subp = stack[-1]
            if subp in utilizations:
                stack.pop()
                continue
            explored = True
            for offset, entry in subp.child_map.items():
                if entry.sub not in utilizations:
                    explored = False
                    stack.append(entry.sub)
            if explored:
                stack.pop()
                utilization = 0
                if len(subp.child_map.items()) == 0 and not subp.name.startswith("noop"):
                    utilization = 1
                for offset, entry in subp.child_map.items():
                    # print(utilizations[entry.sub])
                    utilization += utilizations[entry.sub]
                utilizations[subp] = utilization

        stack = [self.main]
        seen = set()
        while stack:
            subp = stack.pop()
            if subp in seen:
                continue
            seen.add(subp)
            print()
            print(subp.name)
            print('NAME:', subp.name, 'ORDER:', subp.order, 'EFFICIENCY:', utilizations[subp] , '/', 1 << subp.order)
            for offset, entry in sorted(subp.child_map.items()):
                while len(offset) < subp.order:
                    offset = offset + ' '
                display = '    {offset} -> {child}'.format(offset=offset, child=entry.sub.name)
                if entry.goto:
                    display += ' -> ' + entry.goto
                for label in entry.labels or ():
                    display += ' #' + label
                print(display)
                stack.append(entry.sub)

    def reachable(self):
        """Enumerates reachable states for the generated Turing machine."""
        queue = [self.entry]
        seen = []
        seen_set = set()
        while queue:
            state = queue.pop()
            if isinstance(state, Halt) or state in seen_set:
                continue
            if not state.set:
                continue
            seen_set.add(state)
            seen.append(state)
            queue.append(state.next1)
            queue.append(state.next0)
        return seen

    def print_machine(self):
        """Prints the state-transition table for the generated Turing machine."""
        reachable = sorted(self.reachable(), key=lambda x: x.name)

        count = {}
        for state in reachable:
            count[state.name] = count.get(state.name, 0) + 1

        index = {}
        renumber = {}
        for state in reachable:
            if count[state.name] == 1:
                continue
            index[state.name] = index.get(state.name, 0) + 1
            renumber[state] = state.name + '(#' + str(index[state.name]) + ')'

        dirmap = {1: 'r', -1: 'l'}
        for state in sorted(self.reachable(), key=lambda x: x.name):
            print(renumber.get(state, state.name), '=',
                  state.write0, dirmap[state.move0], renumber.get(state.next0, state.next0.name),
                  state.write1, dirmap[state.move1], renumber.get(state.next1, state.next1.name))
            # print(renumber.get(state, state.name), 1, state.write1, dirmap[state.move1], renumber.get(state.next1, state.next1.name))
            # print(renumber.get(state, state.name), "*", state.write0, dirmap[state.move0], renumber.get(state.next0, state.next0.name))

    def tm_print(self):
        """Prints the current state of the Turing machine execution."""
        tape = ''.join(' ' + x for x in self.left_tape) + \
            '[' + self.current_tape + ']' + ' '.join(reversed(self.right_tape))
        print('{state:{len}} {tape}'.format(len=self.longest_label, \
            state=self.state.name, tape=tape))

    def tm_step(self):
        """Executes the Turing machine for a single step."""
        self.tm_print()
        state = self.state

        if self.current_tape == '0':
            write, move, nextstate = state.write0, state.move0, state.next0
        else:
            write, move, nextstate = state.write1, state.move1, state.next1

        self.current_tape = write
        self.state = nextstate

        if move == 1:
            self.left_tape.append(self.current_tape)
            self.current_tape = self.right_tape.pop() if self.right_tape else '0'
        elif move == -1:
            self.right_tape.append(self.current_tape)
            self.current_tape = self.left_tape.pop() if self.left_tape else '0'
        else:
            assert False
