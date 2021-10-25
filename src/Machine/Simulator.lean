import Machine.Parser
import Machine.Options
import Lean.Elab

open Lean Machine.Types

namespace Machine.Types
  def machine.next : machine → machine
  | ⟨program, stack, regs, flag, progc⟩ => ⟨program, stack, regs, flag, progc + 1⟩

  def machine.get (m : machine) (r : reg) : Int :=
  (m.regs.find? r).get!
end Machine.Types

namespace Machine.Simulator
  def condjmp (M : machine) (cond : Ordering) (ptr : Nat) : machine :=
  ⟨M.program, M.stack, M.regs, M.flag, if M.flag == cond then ptr else M.progc + 1⟩

  def instr.eval (M : machine) : instr → IO machine
  | instr.push z => return ⟨M.program, M.stack.push z, M.regs, M.flag, M.progc + 1⟩
  | instr.pushr r => return ⟨M.program, M.stack.push (M.get r), M.regs, M.flag, M.progc + 1⟩
  | instr.popr r => return ⟨M.program, M.stack.pop, M.regs.replace r M.stack.back, M.flag, M.progc + 1⟩
  | instr.dup => return ⟨M.program, M.stack.push M.stack.back, M.regs, M.flag, M.progc + 1⟩
  | instr.add r₁ r₂ r₃ => return ⟨M.program, M.stack, M.regs.replace r₃ (M.get r₁ + M.get r₂), M.flag, M.progc + 1⟩
  | instr.neg r₁ r₂ => return ⟨M.program, M.stack, M.regs.replace r₂ (-M.get r₁), M.flag, M.progc + 1⟩
  | instr.mul r₁ r₂ r₃ => return ⟨M.program, M.stack, M.regs.replace r₃ (M.get r₁ * M.get r₂), M.flag, M.progc + 1⟩
  | instr.cmp r₁ r₂ => return ⟨M.program, M.stack, M.regs, compare (M.get r₁) (M.get r₂), M.progc + 1⟩
  | instr.jmp ptr => return ⟨M.program, M.stack, M.regs, M.flag, ptr⟩
  | instr.je ptr => return (condjmp M Ordering.eq ptr)
  | instr.jg ptr => return (condjmp M Ordering.gt ptr)
  | instr.jl ptr => return (condjmp M Ordering.lt ptr)
  | instr.dump => do println! "r1 = {M.get reg.r1}, r2 = {M.get reg.r2}, r3 = {M.get reg.r3}, r4 = {M.get reg.r4}"; return M.next

  def tick (M : machine) : IO (Option machine) :=
  match M.program.get? M.progc with
  | none   => return none
  | some ε => some <$> instr.eval M ε

  private def turn (M₀ : machine) : Nat → IO Unit
  |   0   => throw (IO.userError "execution depth was reached")
  | n + 1 => do match (← tick M₀) with
    | none   => return ()
    | some M => turn M n

  private partial def unsafeTurn (M₀ : machine) : IO Unit :=
  do match (← tick M₀) with
  | none   => return ()
  | some M => unsafeTurn M

  def simulate (L : Array instr) :=
  unsafeTurn (machine.create L)

  elab "asm " label:ident xs:mnemonic* " end" : command => do
    let M ← Machine.Parser.expand xs
    let xs ← Array.mapM instr.restore M.program
    Elab.Command.elabDeclaration (← `(def $label := #[$xs,*]))

    let opts ← getOptions

    if Machine.Options.debugAsm.get opts then
      do turn M (Machine.Options.executionDepth.get opts)
    else return ()

end Machine.Simulator