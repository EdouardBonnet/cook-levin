import Lax429075.Circuits
import Mathlib.Tactic

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

inductive Expr where
  | wire (index : ℕ)
  | constant (value : Bool)
  | neg (a : Expr)
  | conj (a b : Expr)
  | disj (a b : Expr)

def Expr.eval (ρ : Assignment) : Expr → Bool
  | .wire i => ρ i
  | .constant b => b
  | .neg a => !(a.eval ρ)
  | .conj a b => a.eval ρ && b.eval ρ
  | .disj a b => a.eval ρ || b.eval ρ

def Expr.Bounded (n : ℕ) : Expr → Prop
  | .wire i => i < n
  | .constant _ => True
  | .neg a => a.Bounded n
  | .conj a b | .disj a b => a.Bounded n ∧ b.Bounded n

def Expr.cost : Expr → ℕ
  | .wire _ => 0
  | .constant _ => 1
  | .neg a => a.cost + 1
  | .conj a b | .disj a b => a.cost + b.cost + 1

structure Fragment where
  gates : List Gate
  output : ℕ

def compile (start : ℕ) : Expr → Fragment
  | .wire i => ⟨[], i⟩
  | .constant b => ⟨[.constant b], start⟩
  | .neg a =>
    let f := compile start a
    ⟨f.gates ++ [.neg f.output], start + f.gates.length⟩
  | .conj a b =>
    let f := compile start a
    let g := compile (start + f.gates.length) b
    ⟨f.gates ++ g.gates ++ [.conj f.output g.output], start + f.gates.length + g.gates.length⟩
  | .disj a b =>
    let f := compile start a
    let g := compile (start + f.gates.length) b
    ⟨f.gates ++ g.gates ++ [.disj f.output g.output], start + f.gates.length + g.gates.length⟩

lemma compile_length (start : ℕ) (e : Expr) : (compile start e).gates.length = e.cost := by
  induction e generalizing start with
  | wire i => rfl
  | constant b => rfl
  | neg a ih => simp [compile, Expr.cost, ih]
  | conj a b iha ihb | disj a b iha ihb => simp [compile, Expr.cost, iha, ihb, Nat.add_assoc]

lemma bounded_mono (e : Expr) {a b : ℕ} (h : e.Bounded a) (hab : a ≤ b) : e.Bounded b := by
  induction e with
  | wire i => exact lt_of_lt_of_le h hab
  | constant v => trivial
  | neg e ih => exact ih h
  | conj e f ihe ihf | disj e f ihe ihf => exact ⟨ihe h.1, ihf h.2⟩

lemma compile_output (start : ℕ) (e : Expr) (h : e.Bounded start) :
    (compile start e).output < start + (compile start e).gates.length := by
  cases e with
  | wire i => exact h
  | constant b | neg a | conj a b | disj a b => simp [compile, Nat.add_assoc]

def Ordered (start : ℕ) (gates : List Gate) : Prop :=
  ∀ g i, (g, i) ∈ gates.zipIdx start → ∀ j ∈ g.inputs, j < i

lemma ordered_append (start : ℕ) (as bs : List Gate)
    (ha : Ordered start as) (hb : Ordered (start + as.length) bs) : Ordered start (as ++ bs) := by
  intro g i hm j hj
  rw [List.zipIdx_append] at hm
  rcases List.mem_append.mp hm with h | h
  · exact ha g i h j hj
  · exact hb g i (by simpa [Nat.add_comm] using h) j hj

lemma ordered_singleton (start : ℕ) (g : Gate) (h : ∀ j ∈ g.inputs, j < start) :
    Ordered start [g] := by
  intro q i hm j hj
  have he : (q, i) = (g, start) := by simpa using hm
  cases he
  exact h j hj

end Lax429075Proofs.CircuitBuilder
