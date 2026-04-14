# χRVFormal

本项目是对 RISC-V 处理器 Chisel 设计的指令集一致性进行形式化验证/测试的工具。
其中包括一个可配置的 `RiscvCore` 作为参考模型来表达 RISC-V 指令集规范文档的语义，和一些 `Helper`、`Checker` 来连接待验证处理器与参考模型和设置验证条件。

其中参考模型支持 RV32/64GBCZicsrZifencei，MSU 特权级，基于 Sv39 页表分页方案的虚拟内存。

[English README](README.md)

## 目录 <!-- omit in toc -->

- [χRVFormal](#χrvformal)
  - [安装](#安装)
    - [使用本地发布版本](#使用本地发布版本)
      - [编译参数](#编译参数)
    - [使用托管版本](#使用托管版本)
  - [用法](#用法)
    - [Step 1. 添加 Checker 并设置基本信号](#step-1-添加-checker-并设置基本信号)
      - [参考模型配置选项](#参考模型配置选项)
    - [Step 2. 通过 ConnectHelper 获取更多信号](#step-2-通过-connecthelper-获取更多信号)
      - [获取通用寄存器值](#获取通用寄存器值)
      - [获取特权级相关寄存器值](#获取特权级相关寄存器值)
      - [获取 TLB 访存相关信号值](#获取-tlb-访存相关信号值)
      - [获取访存信号值](#获取访存信号值)
    - [Step 3. 设置验证条件](#step-3-设置验证条件)
    - [Step 4. 通过 ChiselTest 调用形式化验证](#step-4-通过-chiseltest-调用形式化验证)
    - [启用 SingleInstMode 加速单指令验证](#启用-singleinstmode-加速单指令验证)
  - [验证 Verilog 的设计](#验证-verilog-的设计)
    - [Step 1. 通过 JSON 配置文件配置参考模型](#step-1-通过-json-配置文件配置参考模型)
      - [配置文件格式](#配置文件格式)
    - [Step 2. 通过 CLI 生成 `SystemVerilog` 代码](#step-2-通过-cli-生成-systemverilog-代码)
    - [Step 3. 连接 DUT 和 参考模型](#step-3-连接-dut-和-参考模型)
    - [Step 4. 通过 `SymbiYosys` 进行形式化验证](#step-4-通过-symbiyosys-进行形式化验证)
  - [使用建议](#使用建议)
    - [使用 GitHub Actions 进行验证](#使用-github-actions-进行验证)
  - [验证实例](#验证实例)
  - [出版物](#出版物)

## 安装

本项目可以作为项目依赖添加在 Chisel 处理器设计中。
可以[使用本地发布版本](#使用本地发布版本)或者[使用托管版本](#使用托管版本)。

### 使用本地发布版本

由于本项目开发可能造成接口变化，使用本地发布的版本可以自行进行版本控制，避免因为依赖更新造成代码突然无法运行。

下载项目代码并发布到本地：

```shell
git clone https://github.com/iscas-tis/ChiRVFormal.git
cd ChiRVFormal
sbt publishLocal -DHashId=true # 发布版本到本地，并在版本号中添加 HashId
# 和 CHA 一起使用请替换为下述命令，以在项目中依赖 CHA 版本的 Chisel：
# sbt publishLocal -DChiselVersion=CHA -DHashId=true
```

在 `build.sbt` 中添加依赖。

```scala
libraryDependencies += "cn.ac.ios.tis" %% "riscvspeccore" % "1.3-8bb84f4-SNAPSHOT"
```

实际版本号需查看 `sbt publishLocal` 命令的结果，如：

<pre><code>...
[info]  published ivy to ~/.ivy2/local/cn.ac.ios.tis/riscvspeccore_2.13/<strong>1.3-chisel7.0.0-m2-8bb84f4+-SNAPSHOT</strong>/ivys/ivy.xml
...</code></pre>

#### 编译参数

在 `sbt publishLocal` 命令后可以添加参数，配置版本信息和依赖的 Chisel 版本：

`-DHashId=true` 在版本号中显示当前 Git HashId

- 开启前版本号可能为：
  - `1.3-SNAPSHOT`
- 开启后可能为：
  - `1.3-8bb84f4-SNAPSHOT`
  - `1.3-8bb84f4+-SNAPSHOT` (存在未提交的修改)

`-DChiselVerion=<version>` 设置依赖的 Chisel 版本

- 可选版本如：
  - `3.6.0` `6.4.0` `6.5.0` `7.10.0` `CHA`
- 设置后，发布版本号可能为：
  - `1.3-chisel6.4.0-SNAPSHOT`
  - `1.3-chisel7.10.0-8bb84f4-SNAPSHOT`
  - `1.3-cha-8bb84f4-SNAPSHOT`

`-DScalaVersion=<version>` 设置使用的 Scala 版本

- 配合 Chisel 版本使用，如 `2.12.17` `2.13.18`

### 使用托管版本

本项目 main 分支代码会自动编译发布托管到 Maven 仓库，可以直接在项目中直接添加依赖。
托管版本暂不提供 CHA 版本；由于项目在持续开发中，暂不提供托管的正式版，请使用最新 SNAPSHOT 版。
希望锁定依赖版本请[使用本地发布版本](#使用本地发布版本)。

在 `build.sbt` 中添加代码：

```scala
resolvers += Resolver.sonatypeRepo("snapshots") // 添加 SNAPSHOT 版本仓库
libraryDependencies += "cn.ac.ios.tis" %% "riscvspeccore" % "1.3-SNAPSHOT"
```

## 用法

安装成功后按照下述流程，在处理器中添加代码接入验证。
或者可以直接参考我们给出的[例子](#验证实例)。

### Step 1. 添加 Checker 并设置基本信号

`Checker` 是一个硬件电路模块，其中包含一个 RISC-V 参考模型和预设的指令集一致性性质。
通过工具提供的一些接口和方法，可以将处理器指令执行信息传入 `Checker`，组成一个可验证的系统。

`Checker` 需要获取一条指令的完整执行信息，包括指令本身、PC、更新后的寄存器等，可以将 `Checker` 实例化在指令提交级（如写回级）。

```scala

// 1. 设置 Checker 中参考模型 `RiscvCore` 支持的功能
// 此处配置为：
// RV64I 基础指令集，支持 M、C、Zicsr 指令扩展，支持 M/U 两个特权级在
// 在 misa 寄存器中显示支持 A 扩展，但参考模型实际不支持
// pc 的初始值为 "h0000_8000".U
// 支持特权级和sv39的TLB
// 启用内存访问检查和CSR寄存器状态检查
import rvspeccore.core.RVConfig
val rvConfig = RVConfig(
  XLEN = 64,
  extensions = "MCZicsrU",
  fakeExtensions = "A",
  initValue = Map("pc" -> "h0000_8000")
  functions = Seq("Privileged", "TLB")
  formal = Seq("CheckMem", "CheckCSRs")
)

// 2. 实例化 Checker
// 此处实例化一个检查完整寄存器状态的 Checker，不启用额外寄存器路径延迟优化，使用之前设置的参考模型设置
import rvspeccore.checker._
val checker = Module(new CheckerWithState(enableReg = false)(rvConfig))

// 3. 设置指令提交信号
// 当一条指令完全执行结束，所有所需的数据应该准备好，`instCommit.valid` 应该为 true.B
// RiscvCore 将在收到指令后的一个时钟周期内执行这条指令，得到执行结果
// checker 会在同周期内进行状态检查(如果设置了 `enableReg`，则会将输入状态进行寄存，延迟一个周期检查)
checker.io.instCommit.valid := XXX
checker.io.instCommit.excp  := XXX
checker.io.instCommit.inst  := XXX
checker.io.instCommit.pc    := XXX
checker.io.instCommit.npc   := XXX

// 4. 为信号连接工具 ConnectHelper 设置上文创建的 checker
// 在其他模块中获取的信号将通过 ConnectHelper 传递给 checker
// 此处为 CheckerWithResult 类型 Checker 专用的连接工具 ConnectCheckerResult
import rvspeccore.checker._
ConnectHelper.setChecker(checker)(XLEN, rvConfig)
```

目前 `Checker` 中只有 `CheckerWithState` 经过了完全验证，推荐使用。

#### 参考模型配置选项

参考模型具体支持的配置选项如下，详细支持列表见 [acceptKeys](src/main/scala/rvspeccore/core/RVConfig.scala)：

- 位宽 `XLEN: Int`
  - 32、64
- 扩展支持 `extension: String`
  - 默认支持基础指令集 I
  - 扩展指令集
    - "M"：乘除法扩展指令集 M
    - "B"：位操作扩展指令集 B
    - "C"：压缩扩展指令集 C
    - "Zicsr": CSR操作指令集 Zicsr
    - "Zifencei": TODO
  - 特权级
    - 默认支持包含机器级 M
    - "S"：系统级 S（必须和 "U" 同时开启）
    - "U"：用户级 U
- 额外扩展 `fakeExtensions: String`
  - 仅设置 `misa` 寄存器中显示支持该扩展，参考模型实际不支持，可选 "A"-"Z" 任意字母。
- 初始值 `initValue: Map[String, String]`
  - 设置部分寄存器的初始值，如 `pc`、`mstatus`、`mtvec`。
- 功能模块支持 `functions: Seq[String]`
  - "Privileged"：特权级/特权指令功能
  - "TLB"：基于 Sv39 的 TLB
- 形式化验证功能支持 `formal: Seq[String]`
  - "ArbitraryRegFile"：不设置通用寄存器的初始值，使其初始值为任意值（除 x0 寄存器，其值始终为 0）。
    待验证处理器中可以通过 `ArbitraryRegFile.gen` 获得相同的任意初始值。
  - "CheckMem"：检查内存访问
  - "CheckNPC"：检查下一条指令的PC
  - "CheckCSRs"：检查CSR状态

### Step 2. 通过 ConnectHelper 获取更多信号

`ConnectHelper` 封装了一些飞线（`BoringUtils`）方法，可以跨模块获取信号值。
需要注意，获取的所有信号值要和指令提交的时钟同步，可能需要通过 `Reg` 调整。

#### 获取通用寄存器值

对于 `Vec(32, UInt(XLEN.W))` 类型的 `regFile`，可以直接设置寄存器值：

```scala
ConnectHelper.setRegSource(rf)
```

如果不是，需要自行通过 `Vec` 转换格式：

```scala
val regStateWire = Wire(Vec(32, UInt(XLEN.W)))
regStateWire := rf
regStateWire(0) := 0.U // 该例子中 rf 的 x0 值不总是保持 0，此处手工适配
ConnectHelper.setRegSource(regStateWire)
```

#### 获取特权级相关寄存器值

```scala
val privilegeStateWire = ConnectHelper.makePrivilegeSource(rvConfig)
// 当前特权级
privilegeStateWire.mode          := RegNext(priviledgeMode)
// CSR寄存器
privilegeStateWire.csr.mvendorid := RegNext(mvendorid)
privilegeStateWire.csr.marchid   := RegNext(marchid)
// ······
```

#### 获取 TLB 访存相关信号值

通常在待验证处理器的 TLB 模块中获得信号值，需要分析待验证处理器的 TLB 访存状态机。

```scala
val tlbAccessWrie = ConnectHelper.makeTLBSource(if(tlbname == "itlb") false else true)(XLEN)
// 获得访存值
resultTLBWire.read.valid := true.B
resultTLBWire.read.addr  := io.mem.req.bits.addr
resultTLBWire.read.data  := io.mem.resp.bits.rdata
resultTLBWire.read.level := (level-1.U)
// ······
```

#### 获取访存信号值

在待验证处理器对外进行直接访存的时，从中获得相应的值，需要分析待验证处理器的访存状态机。

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

### Step 3. 设置验证条件

对于形式化验证，可以通过 `assume` 设置验证的前置条件，仅验证满足 `assume` 条件下的情况。
本项目提供了工具来判断指令的种类，当指令属于该分类时返回 `true.B`，示例如下：

```scala
import rvspeccore.checker._
val inst = XXX // 完整 32 位指令

// 要求 inst 是 RVI 指令集中的一条指令，位宽为隐式参数 `implicit XLEN: Int`
assume(RVI(inst))
// 要求 inst 是 RVI 指令集中的一条指令，显式指定位宽为 64
assume(RVI(inst)(64))
// 要求 inst 是 RVI 指令集中寄存器和立即数的运算指令
assume(RVI.regImm(inst))
// 要求 inst 是 ADDI 或 ADD 指令
assume(RVI.ADDI(inst) || RVI.ADD(inst))
```

更多指令分类见[代码](src/main/scala/rvspeccore/checker/AssumeHelper.scala)。

### Step 4. 通过 ChiselTest 调用形式化验证

待验证处理器和参考模型连接之后，可以使用测试方法，也可以使用形式化验证在约束的范围内进行检查。

下面通过 [ChiselTest](https://github.com/ucb-bar/chiseltest)
对连接好参考模型的 `DUT` 进行形式化验证，调用了
[BtorMC](https://github.com/Boolector/btor2tools)
模型检测工具，使用 BMC 算法检查了 12 个时钟周期内的指令集一致性：

```scala
import chisel3._
import chiseltest._
import chiseltest.formal._
import org.scalatest.flatspec.AnyFlatSpec

import dut._

class DUTFormalSpec extends AnyFlatSpec with Formal with ChiselScalatestTester {
  behavior of "DUT"
  it should "pass BMC" in {
    verify(new DUT(), Seq(BoundedCheck(12), BtormcEngineAnnotation))
  }
}
```

Chisel3.6/Chisel6 经过测试可以使用对应的 ChiselTest 完成上述验证。
由于 ChiselTest 重放反例中的问题，可能会出现
`ERROR: Constraint #assume was violated!  Warn: Potential simulation/formal mismatch.`
等信息，不影响验证结果。
Chisel7 没有对应版本的 ChiselTest，暂不支持通过 BTOR2 格式的形式化验证。

### 启用 SingleInstMode 加速单指令验证

`checker` 支持使用 `singleInstMode: Option[Inst]` 参数以启用单指令验证模式。当启用单指令验证模式时，`checker` 会自动跳过其他指令，仅保留选定指令的执行验证

```scala
// 仅检查 ADDI 指令执行结果，忽略其他指令
val checker = Module(new CheckerWithState(singleInstMode = Some(RVI.ADDI))(rvConfig))
```

## 验证 Verilog 的设计

### Step 1. 通过 JSON 配置文件配置参考模型

通过创建 `config.json` 配置参考模型 `SystemVerilog` 的编译输出。

```JSON
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

#### 配置文件格式

JSON 配置文件的格式如下，具体含意见[参考模型配置选项](#参考模型配置选项):

- "xlen"：`Number`
- "extensions"：`Array[String]/String`
- "fakeExtensions"：`Array[String]/String`
- "initValue"：`Object[key, String]`
- "functions"：`Array[String]`
- "formal"：`Array[String]`
- "regDelay"：`Boolean`
- "singleInstMode"：`String/NULL`
  - 大小写模糊，指令助记符中的字符`.`允许使用字符`_`代替

### Step 2. 通过 CLI 生成 `SystemVerilog` 代码

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

对于 `Verilog` 的设计，目前仅适配了 `writeback` 参考模型。

可以使用 `-m assume` 来辅助生成指令假设，这需要修改 [InstAssume.scala](sv-core/src/main/scala/svcore/InstAssume.scala) 中的代码，可以使用 [AssumeHelper](#step-3-设置验证条件) 来编写。

### Step 3. 连接 DUT 和 参考模型

对于 `Verilog` 设计，我们提供了两个连接示例：[nerv](sv-core/nerv/)、[picov32](sv-core/picorv32/)，可以参考 `wrapper.sv` 和 `testbench.sv` 中的代码，进行信号导出和连接模型。

### Step 4. 通过 `SymbiYosys` 进行形式化验证

你需要参考[sby文件格式](https://yosyshq.readthedocs.io/projects/sby/en/latest/reference.html#)，来配置 `SymbiYosys`。

如果你使用 `z3`、`boolector` 等求解器运行 BMC 算法，你可以参考以下配置：

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

在终端中运行指令，以启动 `SymbiYosys`：

```bash
> sby -f formal.sby
```

## 使用建议

### 使用 GitHub Actions 进行验证

由于形式化验证所需的时间较长，可以使用 GitHub Actions 服务运行验证任务。
GitHub Actions 可以在每次 push 代码到 GitHub 的时候自动运行验证任务，并且在验证发现错误时发送邮件提醒，保存发现的反例供下载检查。
需要注意，GitHub 的免费运行服务器为[单个 job 限时 6 小时](https://docs.github.com/en/actions/administering-github-actions/usage-limits-billing-and-administration#usage-limits)。

可以参考[该文件](https://github.com/iscas-tis/nutshell-fv/blob/formal/.github/workflows/formal.yml)。
设置执行所需的测试任务，保存输出结果的文件夹。

```yml
      # 执行指定的测试，运行验证任务
      - name: mill Test
        run:  mill "chiselModule[3.6.0]".test
      # 设置要保存的结果目录，执行结束后可以在 Actions 页面下载压缩包
      - name: Archive production artifacts
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: Btormc Output Files
          path: test_run_dir/NutCoreFormal_should_pass
```

## 验证实例

[nutshell-fv](https://github.com/iscas-tis/nutshell-fv)
是在 [NutShell](https://github.com/OSCPU/NutShell) 上使用该项目进行验证的例子。
我们修改了 NutShell 代码以获取验证所需的处理器信息，并与参考模型进行了同步。
最终通过 [ChiselTest](https://github.com/ucb-bar/chiseltest) 提供的接口调用了 BMC 算法进行验证。

[sv-core](https://github.com/E1PsyCongroo/sv-core-fv) 是使用该项目验证 `Verilog` 设计的例子，我们通过 `firtool` 将参考模型转换为 `SystemVerilog` 设计, 为 [nerv](https://github.com/YosysHQ/nerv) 和 [picov32](https://github.com/YosysHQ/picorv32) 提供了 `wrapper` 以获取验证所需的信号，最终使用 `SymbiYosys` 工具使用 `yosys-smtbmc` 引擎调用 `boolector` 求解器进行验证。

## 出版物

如果我们的工作对您有帮助，请引用：

**SETTA 2024: Formal Verification of RISC-V Processor Chisel Designs** [Link](https://link.springer.com/chapter/10.1007/978-981-96-0602-3_8) | [BibTex](https://citation-needed.springer.com/v2/references/10.1007/978-981-96-0602-3_8?format=bibtex&flavour=citation)

**JSA 2026: χRVFormal: Formal Verification of RISC-V Processor Chisel Designs** [Link](https://doi.org/10.1016/j.sysarc.2026.103761) | [BibTex](https://www.sciencedirect.com/sdfe/arp/cite?pii=S1383762126000792&format=text%2Fx-bibtex&withabstract=true)
