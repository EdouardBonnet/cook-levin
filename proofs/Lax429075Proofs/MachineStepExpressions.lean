import Lax429075Proofs.MachineBits

namespace Lax429075Proofs.MachineCircuit

open Turing Lax554803.MachineModels Lax554803.PolynomialTime
open WindowMachine CircuitBuilder

def nextState (M : SingleTape) (q : M.Q) (a : M.Γ) : M.Q :=
  match M.transition q a with
  | none => q
  | some (q', _) => q'

def nextPosition (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ) : Position radius :=
  match M.transition q a with
  | some (_, .move .left) => position radius (coordinate radius i - 1)
  | some (_, .move .right) => position radius (coordinate radius i + 1)
  | _ => i

noncomputable def caseResult (M : SingleTape) (radius : ℕ) (b : Bit M radius)
    (q : M.Q) (i : Position radius) (a : M.Γ) : Expr := by
  classical
  exact match b with
  | .inl q' => .constant (decide (nextState M q a = q'))
  | .inr (.inl i') => .constant (decide (nextPosition M radius q i a = i'))
  | .inr (.inr (j, a')) =>
    match M.transition q a with
    | some (_, .write c) => if j = i then .constant (decide (c = a'))
        else wire M radius (.inr (.inr (j, a')))
    | _ => wire M radius (.inr (.inr (j, a')))

lemma caseResult_bounded (M : SingleTape) (radius : ℕ) (b : Bit M radius)
    (q : M.Q) (i : Position radius) (a : M.Γ) :
    (caseResult M radius b q i a).Bounded (bitCount M radius) := by
  classical
  rcases b with q' | i' | ⟨j, a'⟩
  · trivial
  · trivial
  · unfold caseResult
    cases M.transition q a with
    | none => exact wire_bounded _ _ _
    | some p =>
      obtain ⟨r, op⟩ := p
      cases op with
      | move dir => cases dir <;> exact wire_bounded _ _ _
      | write c =>
        dsimp only
        split_ifs <;> first | trivial | exact wire_bounded _ _ _

lemma caseResult_eval (M : SingleTape) (radius : ℕ) (b : Bit M radius) (c : Cfg M radius) :
    (caseResult M radius b c.state c.head (c.cells c.head)).eval (values (encode M radius c)) =
      bitValue M radius (next M radius c) b := by
  classical
  cases ht : M.transition c.state (c.cells c.head) with
  | none =>
    rcases b with q | i | ⟨j, a⟩ <;>
      simp [caseResult, nextState, nextPosition, ht, next, bitValue, Expr.eval, wire_eval]
  | some p =>
    obtain ⟨q, op⟩ := p
    cases op with
    | move dir =>
      cases dir <;> rcases b with q' | i | ⟨j, a⟩ <;>
        simp [caseResult, nextState, nextPosition, ht, next, bitValue, Expr.eval, wire_eval]
    | write a =>
      rcases b with q' | i | ⟨j, b⟩
      · simp [caseResult, nextState, ht, next, bitValue, Expr.eval]
      · simp [caseResult, nextPosition, ht, next, bitValue, Expr.eval]
      · by_cases hj : j = c.head <;>
          simp [caseResult, ht, hj, next, bitValue, Expr.eval, wire_eval, Function.update_apply]

noncomputable def stepExpr (M : SingleTape) (radius : ℕ) (b : Bit M radius) : Expr :=
  anyExpr ((casesList M radius).map fun s =>
    .conj (guard M radius s.1 s.2.1 s.2.2) (caseResult M radius b s.1 s.2.1 s.2.2))

lemma stepExpr_bounded (M : SingleTape) (radius : ℕ) (b : Bit M radius) :
    (stepExpr M radius b).Bounded (bitCount M radius) := by
  apply anyExpr_bounded
  intro e he
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
  exact ⟨guard_bounded _ _ _ _ _, caseResult_bounded _ _ _ _ _ _⟩

lemma any_select {α : Type} (xs : List α) (a : α) (ha : a ∈ xs) (f : α → Bool) :
    (xs.any fun x => @decide (x = a) (Classical.propDecidable _) && f x) = f a := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.coe_iff_coe, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, _, rfl, hx⟩
    exact hx
  · intro h
    exact ⟨a, ha, rfl, h⟩

lemma guard_select (M : SingleTape) (radius : ℕ) (s : M.Q × Position radius × M.Γ) (c : Cfg M radius) :
    (guard M radius s.1 s.2.1 s.2.2).eval (values (encode M radius c)) =
      @decide (s = (c.state, c.head, c.cells c.head)) (Classical.propDecidable _) := by
  classical
  rw [guard_eval]
  congr 1
  apply propext
  rcases s with ⟨q, i, a⟩
  constructor
  · rintro ⟨hq, hi, ha⟩
    dsimp at hq hi ha
    subst q; subst i; subst a
    rfl
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩

lemma stepExpr_eval (M : SingleTape) (radius : ℕ) (b : Bit M radius) (c : Cfg M radius) :
    (stepExpr M radius b).eval (values (encode M radius c)) = bitValue M radius (next M radius c) b := by
  classical
  simp only [stepExpr, anyExpr_eval, List.any_map, Function.comp_def, Expr.eval, guard_select]
  exact (any_select _ _ (mem_casesList M radius c.state c.head (c.cells c.head))
    (fun s => (caseResult M radius b s.1 s.2.1 s.2.2).eval (values (encode M radius c)))).trans
      (caseResult_eval M radius b c)

noncomputable def stepExpressions (M : SingleTape) (radius : ℕ) : Fin (bitCount M radius) → Expr :=
  fun i => stepExpr M radius ((bitEquiv M radius).symm i)

lemma stepExpressions_eval (M : SingleTape) (radius : ℕ) (c : Cfg M radius) :
    evaluateLayer (stepExpressions M radius) (encode M radius c) = encode M radius (next M radius c) := by
  funext i
  exact stepExpr_eval M radius _ c

end Lax429075Proofs.MachineCircuit
