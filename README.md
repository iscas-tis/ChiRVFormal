# χRVFormal

**χRVFormal** is a formal verification framework for validating the instruction-level correctness of RISC-V processors implemented in Chisel.

It provides:

- A configurable **reference model (`RiscvCore`)** that encodes the RISC-V ISA semantics
- A set of **checkers and helpers** to connect your DUT with the reference model
- Built-in **formal properties** for ISA consistency checking

Read more detailed Chinese README: [中文说明](README.zh-CN.md).

## Table of Contents <!-- omit in toc -->

- [χRVFormal](#χrvformal)
  - [✨ Features](#-features)
  - [🚀 Quick Start](#-quick-start)
    - [1. Add Dependency](#1-add-dependency)
      - [Option A: Local build (recommended)](#option-a-local-build-recommended)
      - [Option B: SNAPSHOT from Maven](#option-b-snapshot-from-maven)
  - [🧩 Usage](#-usage)
    - [Step 1 — Instantiate the Checker](#step-1--instantiate-the-checker)
    - [Step 2 — Connect Commit Signals](#step-2--connect-commit-signals)
    - [Step 3 — Provide Architectural State](#step-3--provide-architectural-state)
      - [General Register](#general-register)
      - [Privilege State](#privilege-state)
      - [TLB](#tlb)
      - [Memory Access](#memory-access)
    - [Step 4 — Add Constraints](#step-4--add-constraints)
    - [Step 5 — Run Formal Verification](#step-5--run-formal-verification)
  - [⚡ Single Instruction Mode](#-single-instruction-mode)
  - [🔌 Verilog Flow (Optional)](#-verilog-flow-optional)
    - [1. Configure model by JSON](#1-configure-model-by-json)
    - [2. Generate SystemVerilog](#2-generate-systemverilog)
    - [3. Run SymbiYosys](#3-run-symbiyosys)
  - [💡 Tips](#-tips)
  - [📂 Examples](#-examples)
  - [📄 Publications](#-publications)

## ✨ Features

- ✅ Supports **RV32/RV64 I**
- ✅ ISA extensions: `M`, `B`, `C`, `Zicsr`, `Zifencei`
- ✅ Privilege modes: `M`, `S`, `U`
- ✅ Virtual memory with **Sv39**
- ✅ Reg/ Memory / CSR / TLB consistency checking
- ✅ Works with **ChiselTest + BMC (BtorMC)**
- ✅ Optional **Verilog flow (SymbiYosys)**

## 🚀 Quick Start

### 1. Add Dependency

#### Option A: Local build (recommended)

```bash
git clone https://github.com/iscas-tis/ChiRVFormal.git
cd ChiRVFormal
sbt publishLocal -DHashId=true
```

Then in your `build.sbt`:

```scala
libraryDependencies += "cn.ac.ios.tis" %% "riscvspeccore" % "<your-version>"
```

#### Option B: SNAPSHOT from Maven

```scala
resolvers += Resolver.sonatypeRepo("snapshots")
libraryDependencies += "cn.ac.ios.tis" %% "riscvspeccore" % "1.3-SNAPSHOT"
```

## 🧩 Usage

### Step 1 — Instantiate the Checker

```scala
val rvConfig = RVConfig(
  XLEN = 64,
  extensions = "MCZicsrU",
  fakeExtensions = "A",
  initValue = Map("pc" -> "h0000_8000"),
  functions = Seq("Privileged", "TLB"),
  formal = Seq("CheckMem", "CheckCSRs")
)

val checker = Module(new CheckerWithState(enableReg = false)(rvConfig))
```

### Step 2 — Connect Commit Signals

Hook your pipeline commit stage:

```scala
checker.io.instCommit.valid := commit_valid
checker.io.instCommit.excp  := commit_excp
checker.io.instCommit.inst  := commit_inst
checker.io.instCommit.pc    := commit_pc
checker.io.instCommit.npc   := commit_npc
```

Initialize helper:

```scala
ConnectHelper.setChecker(checker)(XLEN, rvConfig)
```

### Step 3 — Provide Architectural State

#### General Register

```scala
val regStateWire = Wire(Vec(32, UInt(XLEN.W)))
regStateWire := rf
regStateWire(0) := 0.U
ConnectHelper.setRegSource(regStateWire)
```

#### Privilege State

```scala
val privilegeStateWire = ConnectHelper.makePrivilegeSource(rvConfig)
// cur priviledge mode
privilegeStateWire.mode          := RegNext(priviledgeMode)
// csrs
privilegeStateWire.csr.mvendorid := RegNext(mvendorid)
privilegeStateWire.csr.marchid   := RegNext(marchid)
// ······
```

#### TLB

Get signals in TLB of DUT.

```scala
val tlbAccessWrie = ConnectHelper.makeTLBSource(if(tlbname == "itlb") false else true)(XLEN)
// memory access in TLB
resultTLBWire.read.valid := true.B
resultTLBWire.read.addr  := io.mem.req.bits.addr
resultTLBWire.read.data  := io.mem.resp.bits.rdata
resultTLBWire.read.level := (level-1.U)
// ······
```

#### Memory Access

Get the signal when DUT access memory.

```scala
val memAccessWire = ConnectHelper.makeMemSource()(XLEN)
memAccessWire.read.valid      := isRead
memAccessWire.read.addr       := addr
memAccessWire.read.data       := backend.io.dmem.resp.bits.rdata
memAccessWire.read.memWidth   := width

memAccessWire.write.valid     := isWrite
memAccessWire.write.addr      := addr
memAccessWire.write.data      := wdata
memAccessWire.write.memWidth  := width
```

### Step 4 — Add Constraints

Use `assume` to restrict the input space:

```scala
assume(RVI(inst))
assume(RVI.ADDI(inst))
```

### Step 5 — Run Formal Verification

```scala
verify(new DUT(), Seq(
  BoundedCheck(12),
  BtormcEngineAnnotation
))
```

## ⚡ Single Instruction Mode

Speed up debugging by focusing on one instruction:

```scala
val checker = Module(
  new CheckerWithState(singleInstMode = Some(RVI.ADDI))(rvConfig)
)
```

## 🔌 Verilog Flow (Optional)

### 1. Configure model by JSON

```json
{
  "xlen": 32,
  "extensions": ["I", "Zicsr", "Zba", "Zbb", "Zbc", "Zbs", "Zbkb", "Zbkc", "Zbkx"],
  "fakeExtensions": [],
  "initValue": {"pc": "h8000_0000", "mstatus": "h0000_1800", "mtvec": "h0000_0000"},
  "functions": ["Privileged"],
  "formal": ["CheckMem", "CheckNPC", "CheckCSRs"],
  "regDelay": false,
  "singleInstMode": null
}
```

### 2. Generate SystemVerilog

```bash
> sbt "svcore/runMain svcore.Main -h"
[info] running svcore.Main -h
SystemVerilog Spec Core Generator 1.3
Usage: sv-cores [options]

  -c, --config <file>      path to the configuration file (default: config.json)
  -m, --model <model>      check model to generate (default: writeback)
  -t, --target-dir <directory>
                           directory to output the generated SystemVerilog files (default: build)
  -l, --list               show list of supported models
  -h, --help               show list of command-line options
```

### 3. Run SymbiYosys

config SymbiYosys by `formal.sby`

```cfg
[options]
mode bmc
expect pass,fail
append 0
depth 16
skip 15

[engines]
smtbmc boolector

[script]
read -sv testbench.sv
prep -flatten -nordff -top testbench
chformal -early

[files]
testbench.sv
```

run command:

```bash
sby -f formal.sby
```

## 💡 Tips

- Use **SingleInstMode** first when debugging failures
- Add minimal `assume` constraints to avoid state explosion
- Run formal checks in **CI (GitHub Actions)** to catch regressions early

## 📂 Examples

- NutShell integration: [nutshell-fv](https://github.com/iscas-tis/nutshell-fv)
- SystemVerilog/Verilog examples: [sv-core-fv](https://github.com/E1PsyCongroo/sv-core-fv)

## 📄 Publications

If this project is useful in your research, please cite:

**SETTA 2024: Formal Verification of RISC-V Processor Chisel Designs** [Link](https://link.springer.com/chapter/10.1007/978-981-96-0602-3_8) | [BibTex](https://citation-needed.springer.com/v2/references/10.1007/978-981-96-0602-3_8?format=bibtex&flavour=citation)


**JSA 2026: χRVFormal: Formal Verification of RISC-V Processor Chisel Designs** [Link](https://doi.org/10.1016/j.sysarc.2026.103761) | [BibTex](https://www.sciencedirect.com/sdfe/arp/cite?pii=S1383762126000792&format=text%2Fx-bibtex&withabstract=true)
