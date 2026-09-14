import Lax429075Proofs.TransitionAddresses

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax434930.MachineModels
open MachineCircuit WindowMachine CircuitBuilder

variable {I : Type}

noncomputable def guardCode (M : SingleTape) (radius position base pitch : Number I)
    (q : M.Q) (symbol : M.Γ) : Expression I :=
  Expression.conj (Expression.wire (wireNumber base pitch (.constant (stateIndex M q))))
    (Expression.conj (Expression.wire (wireNumber base pitch (headIndexNumber M position)))
      (Expression.wire (wireNumber base pitch (cellIndexNumber M radius position symbol))))

lemma guardCode_cost (M : SingleTape) (radius position base pitch : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) :
    ((guardCode M radius position base pitch q symbol).value a).cost = 2 := rfl

lemma guardCode_value (M : SingleTape) (radius position base pitch : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) (i : Position (radius.value a))
    (hi : position.value a = i.val) :
    (guardCode M radius position base pitch q symbol).value a =
      (guard M (radius.value a) q i symbol).rename (affineAddress (base.value a) (pitch.value a)) := by
  simp only [guardCode, Expression.conj, Expression.binary, Expression.wire, wireNumber_value,
    headIndexNumber, cellIndexNumber, windowNumber, Number.add, Number.mul, Number.constant,
    hi, MachineCircuit.guard, MachineCircuit.wire, Expr.rename, bitIndex_state, bitIndex_head, bitIndex_cell,
    Bool.true_eq, ite_true]

end Lax429075Proofs.Streaming
