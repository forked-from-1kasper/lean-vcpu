import Machine.Simulator
open Machine.Simulator (simulate)

asm factorial
  -- r2 = -1
  push 1
  pop r2
  neg r2, r2

  -- r3 = 1
  push 1
  pop r3

  -- r4 = 1
  push 1
  pop r4

  -- factorial of N
  push 5

loop:
  pop r1

  mul r1, r3, r3
  add r1, r2, r1
  cmp r1, r4
  push r1

  jg loop

  dump
end

def main : IO Unit :=
simulate factorial