---
name: verilator-simulation
department: "foundry"
description: "Use when planning or reviewing Verilator-based simulation workflows for SystemVerilog designs. Covers lint analysis, simulation setup, trace/waveform debugging, coverage-driven verification, and C++ co-simulation. Do not use for commercial EDA tools (use verification-methodology) or RTL design flow (use chip-design-flow)."
version: 1
triggers:
  - "verilator"
  - "verilator lint"
  - "VCD"
  - "FST"
  - "verilator coverage"
  - "DPI-C"
  - "C++ testbench"
  - "SystemC co-simulation"
---

# Verilator Simulation

## Purpose

Guide Verilator-specific simulation workflows for SystemVerilog designs, from static lint analysis through simulation execution, waveform debugging, coverage closure, and C++ co-simulation integration.

## Scope Constraints

Reviews RTL source, testbenches, and Makefile/build infrastructure. Does not execute Verilator or modify design files. Does not cover commercial simulators (VCS, Questa) or UVM testbench architecture — hand off to verification-methodology for those.

## Inputs

- RTL design files (SystemVerilog)
- Testbench files (directed or constrained-random)
- Build infrastructure (Makefile, scripts)
- Existing Verilator warnings or simulation logs, if any
- Coverage targets or gaps to investigate

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Lint analysis
- [ ] Step 2: Simulation setup
- [ ] Step 3: Trace and waveform debugging
- [ ] Step 4: Coverage-driven verification
- [ ] Step 5: C++ co-simulation
- [ ] Step 6: Limitations and workarounds

### Step 1: Lint Analysis

- Review design files with `--lint-only -Wall --timing -sv` flags.
- Prioritize warnings by security impact: WIDTHTRUNC/WIDTHEXPAND (data corruption), CASEINCOMPLETE (FSM holes), UNOPTFLAT (combinational loops).
- Identify justified suppressions using `/* verilator lint_off WARNING */` pragmas.
- Separate design lint (strict, `-Wall`) from testbench lint (relaxed, `-Wno-STMTDLY -Wno-INITIALDLY`).
- Flag any CMPCONST warnings on range checks — these often mask always-true/always-false comparisons.

### Step 2: Simulation Setup

- Verify `--binary --timing -sv --assert` as baseline flags.
- Confirm `--assert` is present — without it, all SVA assertions are silently ignored.
- Check `--x-assign unique --x-initial unique` for uninitialized register randomization.
- Verify file ordering: design files before testbench files, correct `--top-module`.
- Recommend `-j 0` for parallel C++ compilation and `--Mdir` for separate build directories when running multiple configurations.

### Step 3: Trace and Waveform Debugging

- Recommend `--trace-fst --trace-structs` over `--trace` (VCD) — FST is ~10x smaller and preserves struct field names.
- Verify testbench includes `$dumpfile`/`$dumpvars` or `$test$plusargs("DUMP_VCD")` conditional dump.
- Identify selective tracing with `/* verilator tracing_off */` pragmas for large designs.
- For security-critical paths, identify key signals to watch: tag bits, FSM state, handshake pairs, reservation state.
- Note GTKWave (`brew install --cask gtkwave`) as the standard FST/VCD viewer.

### Step 4: Coverage-Driven Verification

- Enable with `--coverage` flag (line + toggle coverage).
- Post-process with `verilator_coverage --annotate <dir> coverage.dat` for annotated source.
- Identify coverage holes in security-critical paths: FSM transitions, error handling branches, tag-bit toggle.
- Merge coverage across multiple simulation runs for regression.
- Note: Verilator does not support SystemVerilog covergroups — functional coverage requires post-processing or assertion-based coverage.

### Step 5: C++ Co-Simulation

- For DPI-C integration: use `--cc` mode, bind C functions via `import "DPI-C"` in SystemVerilog.
- For custom C++ wrappers: include `verilated.h`, instantiate `Vtop`, step with `eval()`.
- Enable tracing in C++ with `Verilated::traceEverOn(true)` before model construction.
- Reference model integration: compare DUT outputs against C++ golden model each cycle.
- Debug with `VL_PRINTF` and `Verilated::debug(level)`.

### Step 6: Limitations and Workarounds

- No full UVM support — use directed + constrained-random testbenches in pure SystemVerilog.
- Limited SVA — only subset of concurrent assertions supported; `assert property` basic forms work, complex sequences may not.
- Two-state by default — use `--x-assign unique` to catch X-propagation bugs that 2-state hides.
- `--timing` required for `#delay` and `timescale` — without it, clock generation fails.
- `--bbox-unsup` blackboxes unsupported constructs instead of erroring (use cautiously).

> **Compaction resilience**: If context was lost, re-read the Inputs section for the design under review, check the Progress Checklist, then resume from the earliest incomplete step.

## Output Format

### Verilator Workflow Review

| Check Area | Status | Findings | Actions |
|-----------|--------|----------|---------|
| Lint (design) | ... | ... | ... |
| Lint (testbench) | ... | ... | ... |
| Simulation flags | ... | ... | ... |
| Assertions enabled | ... | ... | ... |
| Trace configuration | ... | ... | ... |
| Coverage setup | ... | ... | ... |
| X-safety | ... | ... | ... |

## Handoff

- Hand off to verification-methodology for UVM testbench architecture or commercial simulator flows.
- Hand off to chip-design-flow for synthesis constraints or RTL coding style review.
- Hand off to soc-integration for SoC-level multi-block simulation coordination.
- Hand off to forge/rtl-security-review for security-focused RTL analysis beyond simulation.

## Quality Checks

- [ ] Design files lint-clean with `-Wall` (no unsuppressed warnings)
- [ ] `--assert` flag present in all simulation targets
- [ ] `--x-assign unique` used for X-safety
- [ ] Trace configuration verified (FST preferred, conditional dump in testbench)
- [ ] Coverage targets defined and collection enabled
- [ ] Security-critical signal paths identified for waveform inspection
- [ ] Limitations documented and workarounds in place

## Evolution Notes
<!-- Observations appended after each use -->
