import Std.Data.AssocList
open Std

namespace Machine.Types

inductive reg
| r1 | r2 | r3 | r4
deriving BEq

inductive instr
| push  : Int → instr
| pushr : reg → instr
| popr  : reg → instr
| dup   : instr
| add   : reg → reg → reg → instr
| neg   : reg → reg → instr
| mul   : reg → reg → reg → instr
| cmp   : reg → reg → instr
| jmp   : Nat → instr
| je    : Nat → instr
| jg    : Nat → instr
| jl    : Nat → instr
| dump  : instr

inductive mnemonic
| label     : String → instr → mnemonic
| anonymous : instr → mnemonic

def tape := Array instr

structure machine :=
(stack   : Array Int)
(regs    : AssocList reg Int)
(flag    : Ordering)
(progc   : Nat)

end Machine.Types