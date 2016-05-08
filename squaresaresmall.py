"""Turing machine for conjecturing that all squares are less than 5."""
from framework import Machine, MachineBuilder, memo, Label, Goto

# Let's check whether or not all squares are less than 5

class SquaresAreSmall(MachineBuilder):
    """Turing machine for conjecturing that all squares are less than 5."""
    pc_bits = 8
    def __init__(self):
        super().__init__()
        self.rega, self.regb, self.regc, self.regd = self.regfile('a', 'b', 'c', 'd')

    @memo
    def main(self):
        """Entry point."""
        # while b < 5:
        #     square(a, b)
        #     incr(a)
        #     print b
        return self.makesub(
            Label('again'),
            # square a
            self.transfer(self.rega, self.regb, self.regc),
            self.transfer(self.regb, self.rega),
            # b=a c=0
            Label('mulloop'),
            self.regb.dec,
            Goto('mulend'),
            self.transfer(self.rega, self.regc, self.regd),
            self.transfer(self.regd, self.rega),
            Goto('mulloop'),
            Label('mulend'),
            # c=a*a
            self.regc.dec,
            self.noop(0),
            self.regc.dec,
            self.noop(0),
            self.regc.dec,
            self.noop(0),
            self.regc.dec,
            self.noop(0),
            # c = a*a-4
            self.regc.dec,
            Goto('lessthan5'),
            self.halt(),
            Label('lessthan5'),
            self.transfer(self.regc),
            self.rega.inc,
            Goto('again'),
            name='main()',
        )

Machine(SquaresAreSmall()).harness()
