#!/usr/bin/python3
from framework import *

# Let's check whether or not all squares are less than 5

class SquaresAreSmall(MachineBuilder):
    pc_bits = 8
    def __init__(self):
        super().__init__()
        self.regfile('a', 'b', 'c', 'd')

    @memo
    def main(self):
        # while b < 5:
        #     square(a, b)
        #     incr(a)
        #     print b
        return self.makesub(
            label('again'),
            # square a
            self.transfer(self.a, self.b, self.c),
            self.transfer(self.b, self.a),
            # b=a c=0
            label('mulloop'),
            self.b.dec,
            goto('mulend'),
            self.transfer(self.a, self.c, self.d),
            self.transfer(self.d, self.a),
            goto('mulloop'),
            label('mulend'),
            # c=a*a
            self.c.dec,
            self.noop(0),
            self.c.dec,
            self.noop(0),
            self.c.dec,
            self.noop(0),
            self.c.dec,
            self.noop(0),
            # c = a*a-4
            self.c.dec,
            goto('lessthan5'),
            self.halt(),
            label('lessthan5'),
            self.transfer(self.c),
            self.a.inc,
            goto('again'),
            name='main()',
        )

Machine(SquaresAreSmall()).harness()
