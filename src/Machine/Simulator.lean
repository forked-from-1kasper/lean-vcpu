import Machine.Parser
import Machine.Options
import Lean.Elab

open Lean Machine.Types

namespace Machine.Types
  def machine.next : machine → machine
  | ⟨stack, regs, flag, progc⟩ => ⟨stack, regs, flag, progc + 1⟩

  def machine.get (m : machine) (r : reg) : Int :=
  (m.regs.find? r).get!
end Machine.Types

namespace Machine.Simulator
  def condjmp (M : machine) (cond : Ordering) (ptr : Nat) : machine :=
  ⟨M.stack, M.regs, M.flag, if M.flag == cond then ptr else M.progc + 1⟩

  def instr.eval (M : machine) : instr → machine
  | instr.push z => ⟨M.stack.push z, M.regs, M.flag, M.progc + 1⟩
  | instr.pushr r => ⟨M.stack.push (M.get r), M.regs, M.flag, M.progc + 1⟩
  | instr.popr r => ⟨M.stack.pop, M.regs.replace r M.stack.back, M.flag, M.progc + 1⟩
  | instr.dup => ⟨M.stack.push M.stack.back, M.regs, M.flag, M.progc + 1⟩
  | instr.add r₁ r₂ r₃ => ⟨M.stack, M.regs.replace r₃ (M.get r₁ + M.get r₂), M.flag, M.progc + 1⟩
  | instr.neg r₁ r₂ => ⟨M.stack, M.regs.replace r₂ (-M.get r₁), M.flag, M.progc + 1⟩
  | instr.mul r₁ r₂ r₃ => ⟨M.stack, M.regs.replace r₃ (M.get r₁ * M.get r₂), M.flag, M.progc + 1⟩
  | instr.cmp r₁ r₂ => ⟨M.stack, M.regs, compare (M.get r₁) (M.get r₂), M.progc + 1⟩
  | instr.jmp ptr => ⟨M.stack, M.regs, M.flag, ptr⟩
  | instr.je ptr => (condjmp M Ordering.eq ptr)
  | instr.jg ptr => (condjmp M Ordering.gt ptr)
  | instr.jl ptr => (condjmp M Ordering.lt ptr)
  | instr.dump => M.next

  def instr.effect (M : machine) : instr → IO Unit
  | instr.dump => do println! "r1 = {M.get reg.r1}, r2 = {M.get reg.r2}, r3 = {M.get reg.r3}, r4 = {M.get reg.r4}"
  | _          => return ()

  def tick (M : machine) (ρ : tape) : Option machine :=
  match ρ.get? M.progc with
  | none   => none
  | some ε => some (instr.eval M ε)

  def effect (M : machine) (ρ : tape) : IO Unit :=
  match ρ.get? M.progc with
  | none   => return ()
  | some ε => instr.effect M ε

  private def await (M₀ : machine) (ρ : tape) : Nat → IO Unit
  |   0   => throw (IO.userError "execution depth was reached")
  | n + 1 => do effect M₀ ρ; match tick M₀ ρ with
    | none   => return ()
    | some M => await M ρ n

  private partial def unsafeAwait (M₀ : machine) (ρ : tape) : IO Unit :=
  do effect M₀ ρ; match tick M₀ ρ with
  | none   => return ()
  | some M => unsafeAwait M ρ

  def simulate :=
  unsafeAwait machine.init

  elab "asm " label:ident xs:mnemonic* " end" : command => do
    let (ρ, M) ← Machine.Parser.expand xs
    let xs ← Array.mapM instr.restore ρ
    Elab.Command.elabDeclaration (← `(def $label := #[$xs,*]))

    let opts ← getOptions

    if Machine.Options.debugAsm.get opts then
      do await M ρ (Machine.Options.executionDepth.get opts)
    else return ()

end Machine.Simulator