from framework import *

# Let's check whether or not all squares are less than 5

class SquaresAreSmall(MachineBuilder):
    def __init__(self):
        self.regfile('a', 'b', 'c', 'd')

    @memo
    def square(self, y, x):
        #y = x * x
        return self.makesub(name = 'square({},{})'.format(x.name, y.name),
            self.transfer(x, self.t0, self.t1),
            self.transfer(self.t0, x)
        )

    @memo
    def main(self):
        # while b < 5:
        #     square(a, b)
        #     incr(a)
        #     print b
        return self.makesub(name='main()',
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
            self.nop(0),
            self.c.dec,
            self.nop(0),
            self.c.dec,
            self.nop(0),
            self.c.dec,
            self.nop(0),
            # c = a*a-4
            self.c.dec,
            goto('lessthan5'),
            self.halt(),
            label('lessthan5'),
            self.transfer(self.c),
            self.a.inc,
            goto('again'),
        )

Machine(SquaresAreSmall()).harness()
