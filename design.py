"""FPSAT entry shell: the competition register map, version 1.

You do not need to edit this file. It implements the register map from
spec/register_map_v1.md and connects it to your solver in `solver.py`.

The platform finds the top module of an Amaranth entry as the one Elaboratable
defined in this file that has the Wishbone signals below, so keep `Entry` as
the only such class here. Put anything else in other files.
"""

from amaranth import Cat, Elaboratable, Module, Mux, Signal, signed

from solver import Solver

MAGIC = 0x46505341  # ASCII "FPSA"
VERSION = 1

# Register map v1 (word addresses).
R_CTRL, R_STATUS, R_RESULT = 0, 1, 2
R_NVARS, R_NCLAUSES, R_NLITS = 3, 4, 5
R_LOAD, R_MODEL = 6, 7
R_MAGIC, R_VERSION = 8, 9
# Words 10 and 11 belong to the SoC (solve-cycle counter); the SoC answers them.
R_MAX_VARS, R_MAX_CLAUSES, R_MAX_LITS, R_INFO = 12, 13, 14, 15

# Shell states.
S_IDLE, S_BUSY, S_DONE, S_REJECTED, S_ABORTING = range(5)


class Entry(Elaboratable):
    def __init__(self, solver_cls=Solver):
        self.solver_cls = solver_cls
        # Wishbone B4 slave, fixed by the platform (see the spec, section 1).
        self.wb_cyc = Signal()
        self.wb_stb = Signal()
        self.wb_we = Signal()
        self.wb_adr = Signal(9)
        self.wb_dat_w = Signal(32)
        self.wb_sel = Signal(4)
        self.wb_dat_r = Signal(32)
        self.wb_ack = Signal()

    def elaborate(self, platform):
        m = Module()
        m.submodules.solver = sv = self.solver_cls()
        self.solver = sv

        state = Signal(3)
        nvars, nclauses, nlits = Signal(32), Signal(32), Signal(32)
        result = Signal(2)
        info = Signal(32)
        mptr = Signal(32)  # next model variable to read (0-based)
        abort_cnt = Signal(2)

        adr = self.wb_adr
        ack = self.wb_ack
        idle = state == S_IDLE
        in_window = (adr == R_MODEL) | adr[8]  # word 7 and the 256-511 alias

        # One transaction at a time. `go` is the cycle the request is taken;
        # the ack follows one cycle later and the bridge holds the request
        # until then. A load write waits (no ack) while the solver is not ready.
        req = self.wb_cyc & self.wb_stb & ~ack
        is_load_write = self.wb_we & (adr == R_LOAD)
        go = Signal()
        m.d.comb += go.eq(req & ~(is_load_write & idle & ~sv.load_ready))
        m.d.sync += ack.eq(go)

        wr = go & self.wb_we
        ctrl_wr = wr & (adr == R_CTRL)
        abort_req = ctrl_wr & self.wb_dat_w[1]
        start_req = ctrl_wr & self.wb_dat_w[0] & ~self.wb_dat_w[1] & idle
        size_wr = wr & idle & ((adr == R_NVARS) | (adr == R_NCLAUSES) | (adr == R_NLITS))

        exceeds = (
            (nvars > sv.max_vars)
            | (nclauses > sv.max_clauses)
            | (nlits > sv.max_lits)
        )

        # Instance size registers (ignored unless idle).
        with m.If(wr & idle):
            with m.Switch(adr):
                with m.Case(R_NVARS):
                    m.d.sync += nvars.eq(self.wb_dat_w)
                with m.Case(R_NCLAUSES):
                    m.d.sync += nclauses.eq(self.wb_dat_w)
                with m.Case(R_NLITS):
                    m.d.sync += nlits.eq(self.wb_dat_w)

        # State machine.
        with m.If(abort_req):
            m.d.sync += [
                state.eq(S_ABORTING),
                abort_cnt.eq(0),
                result.eq(0),
                info.eq(0),
                nvars.eq(0),
                nclauses.eq(0),
                nlits.eq(0),
            ]
        with m.Elif(start_req):
            m.d.sync += state.eq(Mux(exceeds, S_REJECTED, S_BUSY))
        with m.Else():
            with m.Switch(state):
                with m.Case(S_BUSY):
                    with m.If(sv.rejected):
                        m.d.sync += state.eq(S_REJECTED)
                    with m.Elif(sv.done):
                        m.d.sync += [
                            result.eq(sv.result),
                            info.eq(sv.info),
                            state.eq(S_DONE),
                        ]
                with m.Case(S_ABORTING):
                    with m.If(abort_cnt != 3):
                        m.d.sync += abort_cnt.eq(abort_cnt + 1)
                    # Stay at least two cycles so the solver sees `abort`.
                    with m.If((abort_cnt >= 2) & sv.idle):
                        m.d.sync += state.eq(S_IDLE)

        # Solver connections.
        m.d.comb += [
            sv.start.eq(start_req & ~exceeds),
            sv.abort.eq(state == S_ABORTING),
            sv.nvars.eq(nvars),
            sv.nclauses.eq(nclauses),
            sv.nlits.eq(nlits),
            sv.load_valid.eq(go & is_load_write & idle),
            sv.load_data.eq(self.wb_dat_w),
            sv.model_addr.eq(mptr),
        ]

        # Model readback. Word 7 and every word in 256-511 pop the same stream.
        model_valid = (state == S_DONE) & (result == 1) & (mptr < nvars)
        var = Signal(32)
        neg_var = Signal(32)
        lit = Signal(signed(32))
        m.d.comb += [
            var.eq(mptr + 1),
            neg_var.eq(-var),
            lit.eq(Mux(sv.model_val, var, neg_var)),
        ]
        pop = ack & self.wb_cyc & self.wb_stb & ~self.wb_we & in_window & model_valid
        with m.If(abort_req | size_wr):
            m.d.sync += mptr.eq(0)
        with m.Elif(pop):
            m.d.sync += mptr.eq(mptr + 1)

        # Reads. Valid in the ack cycle.
        busy = (state == S_BUSY) | (state == S_ABORTING)
        status = Cat(busy, state == S_DONE, state == S_REJECTED)
        with m.Switch(adr):
            with m.Case(R_STATUS):
                m.d.comb += self.wb_dat_r.eq(status)
            with m.Case(R_RESULT):
                m.d.comb += self.wb_dat_r.eq(result)
            with m.Case(R_MAGIC):
                m.d.comb += self.wb_dat_r.eq(MAGIC)
            with m.Case(R_VERSION):
                m.d.comb += self.wb_dat_r.eq(VERSION)
            with m.Case(R_MAX_VARS):
                m.d.comb += self.wb_dat_r.eq(sv.max_vars)
            with m.Case(R_MAX_CLAUSES):
                m.d.comb += self.wb_dat_r.eq(sv.max_clauses)
            with m.Case(R_MAX_LITS):
                m.d.comb += self.wb_dat_r.eq(sv.max_lits)
            with m.Case(R_INFO):
                m.d.comb += self.wb_dat_r.eq(info)
        with m.If(in_window):
            m.d.comb += self.wb_dat_r.eq(Mux(model_valid, lit, 0))

        return m
