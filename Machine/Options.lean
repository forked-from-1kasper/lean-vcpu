import Lean

namespace Machine.Options

register_option debugAsm : Bool := {
  defValue := false
  descr    := "evaluates assembler code while type checking"
}

register_option executionDepth : Nat := {
  defValue := 1000
  descr    := "assembler execution depth"
}

end Machine.Options