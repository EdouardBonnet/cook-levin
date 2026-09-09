import Lax429075.CNF

/-!
---
title: Boolean circuits
type: definition
---
A circuit is a finite sequence of input, constant, negation, conjunction,
and disjunction gates. Every wire refers to an earlier gate, and the output
is a gate of the circuit. A satisfying wire assignment respects every gate
and makes the output true.
-/

namespace Lax429075.Circuits

open CNF

inductive Gate
  | input
  | constant (value : Bool)
  | neg (a : ℕ)
  | conj (a b : ℕ)
  | disj (a b : ℕ)
  deriving DecidableEq

def Gate.inputs : Gate → List ℕ
  | .input | .constant _ => []
  | .neg a => [a]
  | .conj a b | .disj a b => [a, b]

structure Circuit where
  gates : List Gate
  output : Fin gates.length
  ordered : ∀ g i, (g, i) ∈ gates.zipIdx → ∀ j ∈ g.inputs, j < i

def Gate.check (ρ : Assignment) (i : ℕ) : Gate → Bool
  | .input => true
  | .constant b => ρ i == b
  | .neg a => ρ i == !(ρ a)
  | .conj a b => ρ i == (ρ a && ρ b)
  | .disj a b => ρ i == (ρ a || ρ b)

def check (C : Circuit) (ρ : Assignment) : Bool :=
  ρ C.output && C.gates.zipIdx.all (fun gi => gi.1.check ρ gi.2)

def Satisfiable (C : Circuit) : Prop := ∃ ρ, check C ρ = true

end Lax429075.Circuits
