import Lax429075Proofs.TransitionTermCode
import Lax429075Proofs.ExpressionFold

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax434930.MachineModels
open MachineCircuit WindowMachine CircuitBuilder

variable {I : Type}

lemma anyExpr_rename (f : ℕ → ℕ) (es : List Expr) :
    (anyExpr es).rename f = anyExpr (es.map (Expr.rename f)) := by
  induction es <;> simp_all [anyExpr, Expr.rename]

lemma range_map_ofFn {A : Type} (n : ℕ) (f : ℕ → A) (g : Fin n → A)
    (h : ∀ i, f i.val = g i) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < n := by simpa using! hi
    simpa using! h ⟨i, hi'⟩

noncomputable def stepCode (M : SingleTape) (radius base pitch bit : Number I) : Expression I :=
  Expression.fold false (caseCountNumber M radius) (.constant 4)
    (selectedTermCode M (radius.rename some) (base.rename some) (pitch.rename some) (bit.rename some) (.length none))
    (fun _ => Nat.zero_lt_succ 3)
    (fun a i _ => selectedTermCode_cost M _ _ _ _ _ (extend a (List.replicate i true)))

lemma stepCode_cost (M : SingleTape) (radius base pitch bit : Number I) (a : I → Word) :
    ((stepCode M radius base pitch bit).value a).cost = blockSize M (radius.value a) := by
  rw [← Expression.cost_correct]
  simp only [stepCode, Expression.fold, Number.add, Number.mul, Number.constant, caseCountNumber,
    windowNumber, blockSize]
  ring

lemma stepCode_value (M : SingleTape) (radius base pitch bit : Number I) (a : I → Word)
    (b : Bit M (radius.value a)) (hb : bit.value a = ((bitEquiv M (radius.value a)) b).val) :
    (stepCode M radius base pitch bit).value a =
      (stepExpr M (radius.value a) b).rename (affineAddress (base.value a) (pitch.value a)) := by
  change anyExpr ((List.range (Fintype.card M.Q * (2 * radius.value a + 1) * Fintype.card M.Γ)).map
    (fun i => (selectedTermCode M (radius.rename some) (base.rename some) (pitch.rename some)
      (bit.rename some) (Number.length none)).value (extend a (List.replicate i true)))) = _
  simp only [stepExpr, anyExpr_rename, List.map_map, casesList_enumeration, List.map_ofFn]
  apply congrArg anyExpr
  apply range_map_ofFn
  intro c
  have h := selectedTermCode_value M (radius.rename some) (base.rename some) (pitch.rename some)
    (bit.rename some) (Number.length none) (extend a (List.replicate c.val true)) b c
    (by simpa only [Number.rename, extend_some] using! hb)
    (by simp [Number.length, extend])
  exact h

end Lax429075Proofs.Streaming
