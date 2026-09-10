import Lax429075Proofs.TransitionTapeCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder

variable {I : Type}

noncomputable def caseResultCode (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) : Expression I :=
  let Q : Number I := .constant (Fintype.card M.Q)
  Expression.choose (Test.lt bit Q)
    (.constant (Test.eq (.constant (stateIndex M (nextState M q symbol))) bit))
    (Expression.choose (Test.lt bit (Q.add (windowNumber radius)))
      (.constant (Test.eq (nextPositionNumber M radius position q symbol) (bit.sub Q)))
      (tapeResultCode M radius position base pitch bit q symbol))

lemma caseResultCode_cost (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) :
    ((caseResultCode M radius position base pitch bit q symbol).value a).cost = 1 := by
  simp only [caseResultCode, Expression.choose]
  split_ifs <;> first | rfl | exact tapeResultCode_cost _ _ _ _ _ _ _ _ _

lemma caseResultCode_value (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) (i : Position (radius.value a))
    (b : Bit M (radius.value a)) (hi : position.value a = i.val)
    (hb : bit.value a = ((bitEquiv M (radius.value a)) b).val) :
    (caseResultCode M radius position base pitch bit q symbol).value a =
      (caseResult M (radius.value a) b q i symbol).rename (affineAddress (base.value a) (pitch.value a)) := by
  rcases b with q' | j | ⟨j, outputSymbol⟩
  · have hq : stateIndex M q' < Fintype.card M.Q := (Fintype.equivFin M.Q q').isLt
    simp [caseResultCode, Expression.choose, Test.lt, Number.constant, hb, bitIndex_state, hq,
      Expression.constant, Test.eq_value, stateIndex_eq, caseResult, Expr.rename]
  · have hnot : ¬ Fintype.card M.Q + j.val < Fintype.card M.Q := by omega
    have hlt : Fintype.card M.Q + j.val < Fintype.card M.Q + (2 * radius.value a + 1) := by omega
    have hnext := nextPositionNumber_value M radius position q symbol a i hi
    simp [caseResultCode, Expression.choose, Test.lt, Number.constant, Number.add, Number.mul,
      Number.sub, windowNumber, hb, bitIndex_head, hnot, hlt, Expression.constant, Test.eq_value,
      hnext, caseResult, Expr.rename, Fin.ext_iff]
  · have hnot : ¬ ((bitEquiv M (radius.value a)) (.inr (.inr (j, outputSymbol)))).val < Fintype.card M.Q := by
      rw [bitIndex_cell]; omega
    have hnot' : ¬ ((bitEquiv M (radius.value a)) (.inr (.inr (j, outputSymbol)))).val <
        Fintype.card M.Q + (2 * radius.value a + 1) := by rw [bitIndex_cell]; omega
    simp only [caseResultCode, Expression.choose, Test.lt, Number.constant, Number.add, Number.mul,
      windowNumber, hb, hnot, hnot', decide_false, Bool.false_eq_true, ite_false]
    exact tapeResultCode_value M radius position base pitch bit q symbol a i j outputSymbol hi hb

end Lax429075Proofs.Streaming
