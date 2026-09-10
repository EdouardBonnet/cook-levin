import Lax429075Proofs.TransitionResultCode
import Lax429075Proofs.MachineEnumeration

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder

variable {I : Type}

noncomputable def transitionTermCode (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) : Expression I :=
  Expression.conj (guardCode M radius position base pitch q symbol)
    (caseResultCode M radius position base pitch bit q symbol)

lemma transitionTermCode_cost (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) :
    ((transitionTermCode M radius position base pitch bit q symbol).value a).cost = 4 := by
  simp [transitionTermCode, Expression.conj, Expression.binary, Expr.cost, guardCode_cost, caseResultCode_cost]

lemma transitionTermCode_value (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) (i : Position (radius.value a))
    (b : Bit M (radius.value a)) (hi : position.value a = i.val)
    (hb : bit.value a = ((bitEquiv M (radius.value a)) b).val) :
    (transitionTermCode M radius position base pitch bit q symbol).value a =
      (Expr.conj (MachineCircuit.guard M (radius.value a) q i symbol)
        (caseResult M (radius.value a) b q i symbol)).rename (affineAddress (base.value a) (pitch.value a)) := by
  simp only [transitionTermCode, Expression.conj, Expression.binary, Bool.true_eq, ite_true,
    guardCode_value M radius position base pitch q symbol a i hi,
    caseResultCode_value M radius position base pitch bit q symbol a i b hi hb, Expr.rename]

def caseCountNumber (M : SingleTape) (radius : Number I) : Number I :=
  ((Number.constant (Fintype.card M.Q)).mul (windowNumber radius)).mul (.constant (Fintype.card M.Γ))

def caseStateNumber (M : SingleTape) (radius index : Number I) : Number I :=
  (index.div (.constant (Fintype.card M.Γ))).div (windowNumber radius)

def casePositionNumber (M : SingleTape) (radius index : Number I) : Number I :=
  (index.div (.constant (Fintype.card M.Γ))).mod (windowNumber radius)

def caseSymbolNumber (M : SingleTape) (index : Number I) : Number I := index.mod (.constant (Fintype.card M.Γ))

noncomputable def symbolTermCode (M : SingleTape) (radius base pitch bit index : Number I)
    (q : M.Q) : Expression I :=
  Expression.select (caseSymbolNumber M index)
    (List.ofFn fun i : Fin (Fintype.card M.Γ) =>
      transitionTermCode M radius (casePositionNumber M radius index) base pitch bit q (enumeration M.Γ i))
    (transitionTermCode M radius (casePositionNumber M radius index) base pitch bit q default)

lemma symbolTermCode_cost (M : SingleTape) (radius base pitch bit index : Number I)
    (q : M.Q) (a : I → Word) : ((symbolTermCode M radius base pitch bit index q).value a).cost = 4 := by
  apply Expression.select_cost
  · exact transitionTermCode_cost _ _ _ _ _ _ _ _ _
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact transitionTermCode_cost _ _ _ _ _ _ _ _ _

noncomputable def selectedTermCode (M : SingleTape) (radius base pitch bit index : Number I) : Expression I :=
  Expression.select (caseStateNumber M radius index)
    (List.ofFn fun i : Fin (Fintype.card M.Q) => symbolTermCode M radius base pitch bit index (enumeration M.Q i))
    (symbolTermCode M radius base pitch bit index default)

lemma selectedTermCode_cost (M : SingleTape) (radius base pitch bit index : Number I)
    (a : I → Word) : ((selectedTermCode M radius base pitch bit index).value a).cost = 4 := by
  apply Expression.select_cost
  · exact symbolTermCode_cost _ _ _ _ _ _ _ _
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact symbolTermCode_cost _ _ _ _ _ _ _ _

lemma selectedTermCode_value (M : SingleTape) (radius base pitch bit index : Number I) (a : I → Word)
    (b : Bit M (radius.value a))
    (c : Fin (Fintype.card M.Q * (2 * radius.value a + 1) * Fintype.card M.Γ))
    (hb : bit.value a = ((bitEquiv M (radius.value a)) b).val) (hc : index.value a = c.val) :
    (selectedTermCode M radius base pitch bit index).value a =
      (Expr.conj (MachineCircuit.guard M (radius.value a) (caseAt M _ c).1 (caseAt M _ c).2.1 (caseAt M _ c).2.2)
        (caseResult M (radius.value a) b (caseAt M _ c).1 (caseAt M _ c).2.1 (caseAt M _ c).2.2)).rename
          (affineAddress (base.value a) (pitch.value a)) := by
  let p : Fin (Fintype.card M.Q * (2 * radius.value a + 1)) × Fin (Fintype.card M.Γ) := finProdFinEquiv.symm c
  let q : Fin (Fintype.card M.Q) × Fin (2 * radius.value a + 1) := finProdFinEquiv.symm p.1
  have hq : (caseStateNumber M radius index).value a = q.1.val := by
    simp only [caseStateNumber, Number.div, Number.constant, windowNumber, Number.add, Number.mul, hc]
    rfl
  have hs : (caseSymbolNumber M index).value a = p.2.val := by
    simp only [caseSymbolNumber, Number.mod, Number.constant, hc]
    rfl
  have hi : (casePositionNumber M radius index).value a = q.2.val := by
    simp only [casePositionNumber, Number.div, Number.mod, Number.constant, windowNumber, Number.add, Number.mul, hc]
    rfl
  rw [selectedTermCode, Expression.select_ofFn_value _ _ _ a q.1 hq,
    symbolTermCode, Expression.select_ofFn_value _ _ _ a p.2 hs]
  exact transitionTermCode_value M radius (casePositionNumber M radius index) base pitch bit
    (enumeration M.Q q.1) (enumeration M.Γ p.2) a q.2 b hi hb

end Lax429075Proofs.Streaming
