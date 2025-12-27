-- src/MyProofs/Main.lean
import Mathlib.Algebra.Order.Ring.Basic

def hello : String := "Hello, Lean!"

#check hello

def main : IO Unit := do
  IO.println "Hello from MyProofs!"
  IO.println s!"Message: {hello}"
