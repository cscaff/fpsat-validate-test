"""A brute-force SAT solver: try every assignment, check every clause.

This exists to test the competition pipeline end to end, not to compete. It holds the
clause stream in a small memory, then walks through all 2**nvars assignments, and for each
one scans the clauses until one is unsatisfied. It is correct and tiny, and it is slow:
roughly 2**nvars * (nlits + nclauses) cycles in the worst case.

Capacity (declared below): 12 variables, 64 clauses, 192 literals. The clause words, with a
0 after each clause, fit in 256 words.

The interface to the shell is documented at the top of the template's solver.py.
"""

from amaranth import Elaboratable, Module, Mux, Signal, signed
from amaranth.lib.memory import Memory

MAX_WORDS = 256
VAR_BITS = 12


class Solver(Elaboratable):
    max_vars = VAR_BITS
    max_clauses = 64
    max_lits = 192  # 192 literals + 64 terminators = 256 words

    def __init__(self):
        # From the shell.
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        # To the shell.
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()

    def elaborate(self, platform):
        m = Module()

        words = Memory(shape=signed(16), depth=MAX_WORDS, init=[])
        m.submodules.words = words
        wr = words.write_port()
        rd = words.read_port(domain="comb")

        wptr = Signal(range(MAX_WORDS + 1))  # words received
        rptr = Signal(range(MAX_WORDS + 1))  # word being checked
        assign = Signal(VAR_BITS)  # current assignment, bit i = variable i + 1
        limit = Signal(VAR_BITS + 1)  # 2**nvars
        clause_sat = Signal()
        running = Signal()
        finished = Signal()

        m.d.comb += [
            self.load_ready.eq(1),
            self.rejected.eq(0),
            self.info.eq(0),
            # Idle: no loaded clauses and not mid-solve or finished. While `abort` is held the
            # state below is cleared in one cycle, so idle follows right after.
            self.idle.eq(~running & ~finished & (wptr == 0)),
        ]

        # Clause memory: the shell strobes `load_valid` once per word.
        m.d.comb += [
            wr.addr.eq(wptr),
            wr.data.eq(self.load_data[:16]),
            wr.en.eq(self.load_valid & (wptr < MAX_WORDS)),
        ]
        with m.If(self.load_valid & (wptr < MAX_WORDS)):
            m.d.sync += wptr.eq(wptr + 1)

        # The literal under the read pointer, and whether the current assignment makes it true.
        lit = Signal(signed(16))
        var_idx = Signal(range(1 << 5))
        lit_true = Signal()
        m.d.comb += [
            rd.addr.eq(rptr),
            lit.eq(rd.data),
            var_idx.eq(Mux(lit < 0, -lit, lit) - 1),
            lit_true.eq(Mux(lit > 0, assign.bit_select(var_idx, 1), ~assign.bit_select(var_idx, 1))),
        ]

        m.d.sync += self.done.eq(0)
        with m.If(self.abort):
            m.d.sync += [
                wptr.eq(0), rptr.eq(0), assign.eq(0), clause_sat.eq(0),
                running.eq(0), finished.eq(0), self.result.eq(0),
            ]
        with m.Else():
            with m.If(self.start):
                m.d.sync += [
                    running.eq(1), rptr.eq(0), assign.eq(0), clause_sat.eq(0),
                    limit.eq(1 << self.nvars[:4]),
                ]
            with m.If(running):
                with m.If(rptr == wptr):
                    # Every clause held under this assignment: satisfiable.
                    m.d.sync += [running.eq(0), finished.eq(1), self.done.eq(1), self.result.eq(1)]
                with m.Elif(lit == 0):
                    with m.If(clause_sat):
                        m.d.sync += [clause_sat.eq(0), rptr.eq(rptr + 1)]
                    with m.Else():
                        self._next_assignment(m, assign, limit, rptr, clause_sat, running, finished)
                with m.Else():
                    m.d.sync += [clause_sat.eq(clause_sat | lit_true), rptr.eq(rptr + 1)]

        # The model is the assignment that satisfied everything. Read one cycle after the address.
        with m.If(self.model_addr < VAR_BITS):
            m.d.sync += self.model_val.eq(assign.bit_select(self.model_addr[:4], 1))
        with m.Else():
            m.d.sync += self.model_val.eq(0)

        return m

    def _next_assignment(self, m, assign, limit, rptr, clause_sat, running, finished):
        """A clause failed: move to the next assignment, or conclude UNSAT after the last."""
        with m.If((assign + 1) >= limit):
            m.d.sync += [running.eq(0), finished.eq(1), self.done.eq(1), self.result.eq(2)]
        with m.Else():
            m.d.sync += [assign.eq(assign + 1), rptr.eq(0), clause_sat.eq(0)]
