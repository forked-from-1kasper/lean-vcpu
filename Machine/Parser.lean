import Machine.Types
import Lean.Elab

open Std Lean Lean.Syntax Lean.Elab.Command Machine.Types

namespace Machine.Parser

declare_syntax_cat reg
declare_syntax_cat instr

syntax "r1" : reg
syntax "r2" : reg
syntax "r3" : reg
syntax "r4" : reg

syntax "push" num : instr
syntax "push" reg : instr
syntax "pop" reg : instr
syntax "dup" : instr
syntax "add" reg ", " reg ", " reg : instr
syntax "neg" reg ", " reg : instr
syntax "mul" reg ", " reg ", " reg : instr
syntax "cmp" reg ", " reg : instr
syntax "jmp" ident : instr
syntax "je" ident : instr
syntax "jg" ident : instr
syntax "jl" ident : instr
syntax "dump" : instr

end Machine.Parser

namespace Machine.Types.reg
  def expand : Syntax → CommandElabM reg
  | `(reg| r1) => return reg.r1
  | `(reg| r2) => return reg.r2
  | `(reg| r3) => return reg.r3
  | `(reg| r4) => return reg.r4
  | _ => throwError "invalid register"

  def restore : reg → CommandElabM Syntax
  | reg.r1 => `(Machine.Types.reg.r1)
  | reg.r2 => `(Machine.Types.reg.r2)
  | reg.r3 => `(Machine.Types.reg.r3)
  | reg.r4 => `(Machine.Types.reg.r4)
end Machine.Types.reg

def ident (stx : Syntax) := stx.getId.toString

namespace Machine.Types.instr
  def expand (label : String → CommandElabM Nat) : Syntax → CommandElabM instr
  | `(instr| push $i:num) => return instr.push i.isNatLit?.get!
  | `(instr| push $r:reg) => return instr.pushr (← reg.expand r)
  | `(instr| pop $r) => return instr.popr (← reg.expand r)
  | `(instr| dup) => return instr.dup
  | `(instr| add $r₁, $r₂, $r₃) => return instr.add (← reg.expand r₁) (← reg.expand r₂) (← reg.expand r₃)
  | `(instr| neg $r₁, $r₂) => return instr.neg (← reg.expand r₁) (← reg.expand r₂)
  | `(instr| mul $r₁, $r₂, $r₃) => do return instr.mul (← reg.expand r₁) (← reg.expand r₂) (← reg.expand r₃)
  | `(instr| cmp $r₁, $r₂) => return instr.cmp (← reg.expand r₁) (← reg.expand r₂)
  | `(instr| jmp $i) => instr.jmp <$> label (ident i)
  | `(instr| je $i) => instr.je <$> label (ident i)
  | `(instr| jg $i) => instr.jg <$> label (ident i)
  | `(instr| jl $i) => instr.jl <$> label (ident i)
  | `(instr| dump) => return instr.dump
  | stx => throwError "invalid instruction “{stx}”"

  def restore : instr → CommandElabM Syntax
  | instr.push i => `(Machine.Types.instr.push $(mkNumLit (toString i)))
  | instr.pushr r => do `(Machine.Types.instr.pushr $(← reg.restore r))
  | instr.popr r => do `(Machine.Types.instr.popr $(← reg.restore r))
  | instr.dup => `(Machine.Types.instr.dup)
  | instr.add r₁ r₂ r₃ => do `(Machine.Types.instr.add $(← reg.restore r₁) $(← reg.restore r₂) $(← reg.restore r₃))
  | instr.neg r₁ r₂ => do `(Machine.Types.instr.neg $(← reg.restore r₁) $(← reg.restore r₂))
  | instr.mul r₁ r₂ r₃ => do `(Machine.Types.instr.mul $(← reg.restore r₁) $(← reg.restore r₂) $(← reg.restore r₃))
  | instr.cmp r₁ r₂ => do `(Machine.Types.instr.cmp $(← reg.restore r₁) $(← reg.restore r₂))
  | instr.jmp ptr => `(Machine.Types.instr.jmp $(mkNumLit (toString ptr)))
  | instr.je ptr => `(Machine.Types.instr.je $(mkNumLit (toString ptr)))
  | instr.jg ptr => `(Machine.Types.instr.jg $(mkNumLit (toString ptr)))
  | instr.jl ptr => `(Machine.Types.instr.jl $(mkNumLit (toString ptr)))
  | instr.dump => `(Machine.Types.instr.dump)
end Machine.Types.instr

declare_syntax_cat mnemonic
syntax ident ": " instr : mnemonic
syntax instr : mnemonic

namespace Machine.Types.mnemonic
  def expand (idx : Nat) : Syntax → Option String × Nat × Syntax
  | `(mnemonic|$e:ident: $τ) => (some (ident e), idx, τ)
  | `(mnemonic|$τ:instr) => (none, idx, τ)
  | _ => unreachable!
end Machine.Types.mnemonic

namespace Machine.Types
  private def zeroes : AssocList reg Int :=
  [(reg.r1, 0), (reg.r2, 0), (reg.r3, 0), (reg.r4, 0)].toAssocList

  def machine.init : machine :=
  ⟨Array.empty, zeroes, Ordering.eq, 0⟩
end Machine.Types

namespace Machine.Parser
  private def extLabel (xs : AssocList String Nat) (x : String) : CommandElabM Nat :=
  match xs.find? x with
  | some idx => return idx
  | none     => throwError "unknown label “{x}”"

  def expand (stx : Array Syntax) : CommandElabM (tape × machine) := do
    let xs := stx.mapIdx (λ idx σ => mnemonic.expand idx.val σ)
    let ys := (Array.foldl (λ map =>
      λ | (none, _, _)   => map
        | (some k, v, _) => map.insert k v)
      AssocList.empty xs)

    let ρ ← Array.mapM (instr.expand (extLabel ys)) (xs.map (λ (_, _, σ) => σ))
    return (ρ, machine.init)
end Machine.Parser
