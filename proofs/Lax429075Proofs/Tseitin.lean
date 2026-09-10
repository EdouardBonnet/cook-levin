import Lax429075.GateCorrect
import Lax429075.TseitinCorrect
import Mathlib.Tactic

namespace Lax429075Proofs

open Lax429075 Lax429075.CNF Lax429075.Circuits Lax429075.Tseitin

/--
---
conclusion: Lax429075.GateCorrect.correct
assumptions:
---
Check the finite truth tables of the five gate forms.
-/
lemma gate_correct (i : ℕ) (g : Gate) (ρ : Assignment) :
    eval (gateClauses i g) ρ = g.check ρ i := by
  cases g with
  | input => rfl
  | constant b =>
    cases b <;> cases hi : ρ i <;>
      simp [gateClauses, eval, Literal.eval, Gate.check, hi]
  | neg a =>
    cases hi : ρ i <;> cases ha : ρ a <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha]
  | conj a b =>
    cases hi : ρ i <;> cases ha : ρ a <;> cases hb : ρ b <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha, hb]
  | disj a b =>
    cases hi : ρ i <;> cases ha : ρ a <;> cases hb : ρ b <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha, hb]

lemma eval_append (F H : Formula) (ρ : Assignment) :
    eval (F ++ H) ρ = (eval F ρ && eval H ρ) := by simp [eval]

lemma eval_flatMap {α : Type} (as : List α) (f : α → Formula) (ρ : Assignment) :
    eval (as.flatMap f) ρ = as.all (fun a => eval (f a) ρ) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons, eval_append, List.all_cons, ih]

/--
---
conclusion: Lax429075.TseitinCorrect.correct
assumptions:
  - Lax429075.GateCorrect.correct
---
Conjoin the gate equivalences with the unit output clause.
-/
lemma tseitin_correct (C : Circuit) : CNF.Satisfiable (Tseitin.encode C) ↔ Circuits.Satisfiable C := by
  have h (ρ : Assignment) : eval (Tseitin.encode C) ρ = check C ρ := by
    unfold Tseitin.encode
    rw [eval_append, eval_flatMap]
    simp_rw [GateCorrect.correct]
    simp [eval, Literal.eval, positive, check]
  simp only [CNF.Satisfiable, Circuits.Satisfiable, h]

end Lax429075Proofs
