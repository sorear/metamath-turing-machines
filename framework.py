# Tape layout: PC:bit[NNN] ( !fence:bit lcursor:bit 0 1* 0 )* .
# each thing after the PC is a unary register.
# to make initial tape state (all zero) useful, fence is active low and cursor
# is one for all cells _left_ of the cursor.
# the cursor may never touch the right fence.
# There is a "dispatch" state which assumes the head is at position zero, and
# reads PC bits through a decision tree to find out what to do.
# The decision tree has shared subtrees - this is how we handle "subroutines".
# Naturally these shared subtrees have to handle different "contexts".
# we shift 1 left of the PC MSB during carry phases.  If this is a problem for
# you, add an extra state to shift right at the beginning.

from collections import namedtuple

class Halt:
    pass

class State:
    def be(self, name, move = None, next = None, write = None,
            move0 = None, next0 = None, write0 = None,
            move1 = None, next1 = None, write1 = None):
        assert not self.set
        self.set = True
        self.name = name
        self.move0 = move0 or move
        self.move1 = move1 or move
        self.next0 = next0 or next
        self.next1 = next1 or next
        self.write0 = write0 or write or '0'
        self.write1 = write1 or write or '1'
        assert self.move0 in -1, 1
        assert self.move1 in -1, 1
        assert self.write0 in '0', '1'
        assert self.write1 in '0', '1'
        assert isinstance(self.name, str)
        assert isinstance(self.next0, State) or isinstance(self.next0, Halt)
        assert isinstance(self.next1, State) or isinstance(self.next1, Halt)

    def clone(self, other):
        assert isinstance(other, State) and other.set
        self.be(name=other.name, move0=other.move0, next0=other.next0,
            write0=other.write0, move1=other.move1, next1=other.next1,
            write1=other.write1)

def lazy(func):
    prop_name = '_' + func.__name__
    def getter(self):
        value = getattr(self, prop_name)
        if not value:
            value = func(self)
            setattr(self, prop_name, value)
        return value

    return property(getter)

label = namedtuple('label', ['name'])
goto = namedtuple('goto', ['name'])

class Subroutine:
    def __init__(self, entry, order, name, fakelevel = None, fakefunc = None):
        self.entry = entry
        self.name = name
        self.order = order
        self.fakelevel = fakelevel
        self.fakefunc = fakefunc

def make_dispatcher(child_map, name, order, at_prefix = ''):
    if child_map[at_prefix]:
        return child_map[at_prefix].entry
    assert len(at_prefix) <= order
    switch = State()
    switch.be(move = 1, name = name + '[' + at_prefix + ']',
        next0 = make_dispatcher(child_map, name, order, at_prefix + '0'),
        next1 = make_dispatcher(child_map, name, order, at_prefix + '1'))
    return switch

class MachineBuilder:
    pc_bits = 0
    quick = 0
    # Quick=0: Print TM
    # Quick=1: Simulate TM, print all steps
    # Quick=2: Simulate TM, print at dispatch
    # Quick=3: Simulate compressed register machine
    # Quick=4: as Quick=3 except subroutines can cheat
    # Quick=5: subroutines can cheat to the extent of storing non-integers

    def __init__(self):
        self._noop = []

    # leaf procs which implement shifting and register machine operations
    # on entry to a leaf proc the tape head is just after the PC
    # shifting off the left end = UB

    @lazy
    def cursor_left(self):
        (scan_fence, scan_cursor, scan_lend, scan_reg, move_fence,
            move_rend, move_reg, move_cursor) = State() for range(8)
        # Skip right until we find the register with cursor=0
        scan_fence.be(move=1, next=scan_cursor, name='left.scan.fence')
        scan_cursor.be(move0=-1, next0=move_fence,   move1=1, next1=scan_lend, name='left.scan.cursor')
        scan_lend.be(move=1, next=scan_reg, name='left.scan.lend')
        scan_reg.be(move=1, next0=scan_fence, next1=scan_reg, name='left.scan.reg')

        # Skip one left
        move_fence.be(move=-1, next=move_rend, name='left.move.fence')
        move_rend.be(move=-1, next=move_reg, name='left.move.rend')
        move_reg.be(move=-1, next0=move_cursor, next1=move_reg, name='left.move.reg')

        # Clear left-of-cursor bit
        move_cursor.be(move=-1, next=self.common_reset.fence, write='0', name='left.move.cursor')

        # Skip left until first=1
        # Fall into nextstate()
        # (handled in common_reset)

        return Subroutine(scan_fence, 0, 'cursor_left')

    @lazy
    def cursor_home(self):
        (scan_fence, scan_fence_0, scan_cursor, scan_lend,
            scan_reg) = State() for range(5)
        # Just skip to the end and clear all the cursor bits
        scan_fence_0.be(move=1, next=scan_cursor, name='home.scan.fence_0')
        scan_cursor.be(move=1, next=scan_lend, write='0', name='home.scan.cursor')
        scan_lend.be(move=1, next=scan_reg, name='home.scan.lend')
        scan_reg.be(move=1, next0=scan_fence, next1=scan_reg, name='home.scan.reg')
        scan_fence.be(move0=-1, next0=self.common_reset.rend, move1=1, next=scan_cursor, name='home.scan.fence')

        return Subroutine(scan_fence_0, 0, 'cursor_home')

    @lazy
    def cursor_right(self):
        # this is the only place we adjust the fences
        (scan_fence, scan_cursor, scan_lend, scan_reg, move_lend, move_reg,
            move_fence) = State() for range(7)

        # skip right until we find the first cursor=0
        scan_fence.be(move=1, next=scan_cursor, name='right.scan.fence')
        scan_cursor.be(move=1, next0=move_lend, write0='1', next1=scan_lend, name='right.scan.cursor')
        scan_lend.be(move=1, next=scan_reg, name='right.scan.lend')
        scan_reg.be(move=1, next0=scan_fence, next1=scan_reg, name='right.scan.reg')

        # we just set the cursor bit.  need to ensure we didn't just land on
        # the right fence -> clear !fence bit on where we landed.
        move_lend.be(move=1, next=move_reg, name='right.move.lend')
        move_reg.be(move=1, next0=move_fence, next1=move_reg, name='right.move.reg')
        move_fence.be(move=-1, next=self.common_reset.rend, write='0', name='right.move.fence')

        return Subroutine(scan_fence, 0, 'cursor_right')

    @lazy
    def cursor_incr(self):
        (scan_fence, scan_cursor, scan_lend, scan_reg, shift_start_lend,
            shift_reg_1, shift_fence, shift_cursor, shift_lend,
            shift_reg_0) = State() for range(10)
        # find the cursor
        scan_fence.be(move=1, next=scan_cursor, name='incr.scan.fence')
        scan_cursor.be(move=1, next1=scan_lend, next0=shift_start_lend, name='incr.scan.cursor')
        scan_lend.be(move=1, next=scan_reg, name='incr.scan.lend')
        scan_reg.be(move=1, next0=scan_fence, next1=scan_reg, name='incr.scan.reg')

        # insert a 1 and shift everything right until the fence
        shift_start_lend.be(move=1, next=shift_reg_1, name='incr.shift.start_lend')
        shift_reg_1.be(move=1, write='1', next0=shift_fence, next1=shift_reg_1, name='incr.shift.reg_1')
        shift_fence.be(move=1, write='0', next0=self.common_reset.rend, next1=shift_cursor, name='incr.shift.fence')
        shift_cursor.be(move=1, write='1', next=shift_lend, name='incr.shift.cursor')
        shift_lend.be(move=1, write='0', next=shift_reg_0, name='incr.shift.lend')
        shift_reg_0.be(move=1, write='0', next0=shift_fence, next1=shift_reg_1, name='incr.shift.reg_0')

        # scroll back (handled in common_reset)
        return Subroutine(scan_fence, 0, 'cursor_incr')

    @lazy
    def cursor_decr(self):
        (scan_fence, scan_cursor, scan_lend, scan_reg, seek_lend_0,
            seek_reg_0, bail_lend, bail_cursor, seek_reg, seek_fence,
            seek_cursor, seek_lend, shift_rend_0, shift_rend_1, shift_reg_0,
            shift_reg_1, shift_cursor, shift_fence,
            fixup_lend) = State() for range(19)
        # find the cursor
        scan_fence.be(move=1, next=scan_cursor, name='decr.scan.fence')
        scan_cursor.be(move=1, next1=scan_lend, next0=seek_lend_0, write0='1', name='decr.scan.cursor')
        scan_lend.be(move=1, next=scan_reg, name='decr.scan.lend')
        scan_reg.be(move=1, next1=scan_reg, next0=scan_fence, name='decr.scan.reg')

        # bail if zero
        seek_lend_0.be(move=1, next=seek_reg_0, name='decr.seek.lend_0')
        seek_reg_0.be(move1=1, next1=seek_reg, move0=-1, next0=bail_lend, name='decr.seek.reg_0')
        bail_lend.be(move=-1, next=bail_cursor, name='decr.bail.lend')
        bail_cursor.be(move=-1, write='0', next=self.common_reset.fence, name='decr.bail.cursor')

        # temporarily move it right (done by scan_cursor)
        # keep going until the right fence
        seek_reg.be(move=1, next0=seek_fence, next1=seek_reg, name='decr.seek.reg')
        seek_fence.be(move0=-1, next0=shift_rend_0, move1=1, next1=seek_cursor, name='decr.seek.fence')
        seek_cursor.be(move=1, next=seek_lend, name='decr.seek.cursor')
        seek_lend.be(move=1, next=seek_reg, name='decr.seek.lend')

        # shift everything left until the cursor, then shift that too
        shift_rend_0.be(write='0', move=-1, next=shift_reg_0, name='decr.shift.rend_0')
        shift_rend_1.be(write='1', move=-1, next=shift_reg_0, name='decr.shift.rend_1')
        shift_reg_0.be(write='0', move=-1, next1=shift_reg_1, next0=shift_cursor, name='decr.shift.reg_0')
        shift_reg_1.be(write='1', move=-1, next1=shift_reg_1, next0=shift_cursor, name='decr.shift.reg_1')
        shift_cursor.be(write0='0', move0=-1, next0=shift_fence, write1='0', move1=1, next1=fixup_lend, name='decr.shift.cursor')
        shift_fence.be(write='0', move=-1, next=shift_rend_1, name='decr.shift.fence')

        fixup_lend.be(write='0', move=-1, next=self.common_reset.cursor_skip, name='decr.fixup.lend')

        return Subroutine(scan_fence, 0, 'cursor_decr')

    @lazy
    def common_reset(self):
        (reset_fence, reset_rend, reset_reg, reset_cursor, reset2_fence,
            reset2_rend, reset2_reg, reset2_cursor) = State() for range(8)
        # handles restoring the tape head and nextstateing for all except dec() success case
        # in all cases we are before the right fence

        reset_fence.be(move=-1, next1=reset_rend, next0=self.nextstate, name='reset.fence')
        reset_rend.be(move=-1, next=reset_reg, name='reset.rend')
        reset_reg.be(move=-1, next0=reset_cursor, next1=reset_reg, name='reset.reg')
        reset_cursor.be(move=-1, next=reset_fence, name='reset.cursor')

        reset2_fence.be(move=-1, next1=reset2_rend, next0=self.nextstate_2, name='resetskip.fence')
        reset2_rend.be(move=-1, next=reset2_reg, name='resetskip.rend')
        reset2_reg.be(move=-1, next0=reset2_cursor, next1=reset2_reg, name='resetskip.reg')
        reset2_cursor.be(move=-1, next=reset2_fence, name='resetskip.cursor')

        # this is not a subroutine!
        return namedtuple('common_reset', ['cursor_skip', 'fence',
            'rend'])(reset2_cursor, reset_fence, reset_rend)

    # Implementing the subroutine model

    @lazy
    def dispatchroot(self):
        # enter me with the tape head on the start of the PC
        return State()

    # these two are entered with the tape on the last PC bit
    @lazy
    def nextstate(self):
        return self.dispatch_order[0][1]

    @lazy
    def nextstate_2(self):
        nextstate_2 = State()
        nextstate_2.be(move=-1, next=self.dispatch_order[1][1], name='nextstate_2')
        return nextstate_2

    @lazy
    def dispatch_order(self):
        table = [[State() for range(2)] for range(self.pc_bits)]

        table[self.pc_bits] = [self.dispatchroot, self.dispatchroot]
        for bit in range(self.pc_bits):
            table[bit][0].be(next=table[bit+1][0], move=-1,
                name='dispatch.'+bit)
            table[bit][1].be(write0='1', next0=table[bit+1][0], write1='0',
                next1=table[bit+1][1] move=-1, name='dispatch.'+bit+'.carry')

        return table

    def noop(self, order):
        reverse = State()
        reverse.be(move=-1, next=self.dispatch_order[order][1], name='noop.'+order)
        return Subroutine(reverse, order, 'noop.'+order)

    def jump(self, rel_pc):
        steps = [State() for range(len(rel_pc) + 1)]
        steps[0].be(move=-1, next=steps[1], name='jump.{}.0'.format(rel_pc))
        steps[len(rel_pc)+1] = self.dispatch_order[len(rel_pc)][0]
        for i in range(len(rel_pc)):
            steps[i+1].be(move=-1, next=steps[i+2], write=rel_pc[-i-1],
                name='jump.{}.{}'.format(rel_pc, i+1))

        return Subroutine(steps[0], 0, 'jump.{}'.format(rel_pc))

    def makesub(self, *parts, name):
        # first find out where everything is and how big I am

        label_offsets = {}
        real_parts = []
        offset = 0

        for part in parts:
            if isinstance(part, label):
                # labels take up no space
                label_offsets[part.name] = offset
                continue

            size = 1 if isinstance(part, goto) else 1 << part.order

            # parts must be aligned
            while offset % size:
                noop_order = (offset & -offset).bit_length() - 1
                offset += 1 << noop_order
                real_parts.push(self.noop(noop_order))

            real_parts.push(part)

        order = 0
        while offset > (1 << order):
            order += 1

        while offset < (1 << order):
            noop_order = (offset & -offset).bit_length() - 1
            offset += 1 << noop_order
            real_parts.push(self.noop(noop_order))

        offset = 0
        child_map = {}

        for part in real_parts:
            if isinstance(part, goto):
                assert part.name in label_offsets
                part = self.jump('{:0{order}b}'.format(label_offsets[part.name], order = order))
            child_map['{:0{order}b}'.format(offset >> part.order, order = order - part.order)] = part

        return Subroutine(make_dispatcher(child_map, name), order, name)

