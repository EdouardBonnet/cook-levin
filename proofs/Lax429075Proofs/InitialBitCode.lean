import Lax429075Proofs.InitialCellCodeCorrectness
import Lax429075Proofs.ExpressionSelection
import Lax429075Proofs.MachineBitAddresses
import Lax429075Proofs.InitialCircuit

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax434930.MachineModels
open CertificateCircuit CircuitBuilder MachineCircuit WindowMachine
open scoped Classical

variable {I : Type}

def windowNumber (radius : Number I) : Number I := ((Number.constant 2).mul radius).add (.constant 1)

def cellOffset (M : SingleTape) (radius bit : Number I) : Number I :=
  bit.sub ((Number.constant (Fintype.card M.Q)).add (windowNumber radius))

def cellPositionNumber (M : SingleTape) (radius bit : Number I) : Number I :=
  (cellOffset M radius bit).div (.constant (Fintype.card M.Γ))

def cellSymbolNumber (M : SingleTape) (radius bit : Number I) : Number I :=
  (cellOffset M radius bit).mod (.constant (Fintype.card M.Γ))

noncomputable def initialBitCode (M : SingleTape) (input : I) (bound radius bit : Number I) : Expression I :=
  let Q : Number I := .constant (Fintype.card M.Q)
  let position := cellPositionNumber M radius bit
  let cells := Expression.select (cellSymbolNumber M radius bit)
    (List.ofFn (fun i : Fin (Fintype.card M.Γ) =>
      initialCellCode M input bound radius position ((Fintype.equivFin M.Γ).symm i)))
    (initialCellCode M input bound radius position default)
  Expression.choose (Test.lt bit Q)
    (Expression.pad 5 (.constant (Test.eq (.constant (stateIndex M default)) bit)))
    (Expression.choose (Test.lt bit (Q.add (windowNumber radius)))
      (Expression.pad 5 (.constant (Test.eq radius (bit.sub Q)))) cells)

lemma initialBitCode_cost (M : SingleTape) (input : I) (bound radius bit : Number I) (a : I → Word) :
    ((initialBitCode M input bound radius bit).value a).cost = 11 := by
  simp only [initialBitCode, Expression.choose]
  split_ifs
  · simp [Expression.pad_value, Expression.constant, pad_cost, Expr.cost]
  · simp [Expression.pad_value, Expression.constant, pad_cost, Expr.cost]
  · apply Expression.select_cost
    · exact initialCellCode_cost _ _ _ _ _ _ _
    · intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact initialCellCode_cost _ _ _ _ _ _ _

lemma stateIndex_eq (M : SingleTape) (q q' : M.Q) : stateIndex M q = stateIndex M q' ↔ q = q' := by
  simp [stateIndex, Fin.val_inj]

lemma symbolIndex_eq (M : SingleTape) (s s' : M.Γ) : symbolIndex M s = symbolIndex M s' ↔ s = s' := by
  simp [symbolIndex, Fin.val_inj]

lemma position_zero_value (radius : ℕ) : (position radius 0).val = radius := by
  simp [position, Nat.mod_eq_of_lt (show radius < 2 * radius + 1 by omega)]

lemma cellOffset_address (Q W i G a : ℕ) : Q + W + i * G + a - (Q + W) = G * i + a := by
  calc
    Q + W + i * G + a - (Q + W) = i * G + a := by omega
    _ = G * i + a := by rw [Nat.mul_comm]

lemma cellPositionNumber_address (M : SingleTape) (radius bit : Number I) (a : I → Word)
    (i : Position (radius.value a)) (symbol : M.Γ)
    (hb : bit.value a = ((bitEquiv M (radius.value a)) (.inr (.inr (i, symbol)))).val) :
    (cellPositionNumber M radius bit).value a = i.val := by
  have hs : symbolIndex M symbol < Fintype.card M.Γ := (Fintype.equivFin M.Γ symbol).isLt
  simp only [cellPositionNumber, cellOffset, windowNumber, Number.div, Number.sub, Number.add,
    Number.mul, Number.constant, hb, bitIndex_cell, cellOffset_address]
  rw [Nat.mul_add_div (alphabet_positive M), Nat.div_eq_of_lt hs, Nat.add_zero]

lemma cellSymbolNumber_address (M : SingleTape) (radius bit : Number I) (a : I → Word)
    (i : Position (radius.value a)) (symbol : M.Γ)
    (hb : bit.value a = ((bitEquiv M (radius.value a)) (.inr (.inr (i, symbol)))).val) :
    (cellSymbolNumber M radius bit).value a = symbolIndex M symbol := by
  have hs : symbolIndex M symbol < Fintype.card M.Γ := (Fintype.equivFin M.Γ symbol).isLt
  simp only [cellSymbolNumber, cellOffset, windowNumber, Number.mod, Number.sub, Number.add,
    Number.mul, Number.constant, hb, bitIndex_cell, cellOffset_address]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

lemma Expression.select_ofFn_value {n : ℕ} (index : Number I) (es : Fin n → Expression I)
    (fallback : Expression I) (a : I → Word) (i : Fin n) (hi : index.value a = i.val) :
    (Expression.select index (List.ofFn es) fallback).value a = (es i).value a := by
  simp [Expression.select_value, hi, i.isLt]

lemma initialBitCode_value (M : SingleTape) (input : I) (bound radius bit : Number I) (a : I → Word)
    (b : Bit M (radius.value a)) (hb : bit.value a = ((bitEquiv M (radius.value a)) b).val) :
    (initialBitCode M input bound radius bit).value a =
      initialBit M (a input) (bound.value a) (radius.value a) b := by
  rcases b with q | i | ⟨i, symbol⟩
  · have hq : stateIndex M q < Fintype.card M.Q := (Fintype.equivFin M.Q q).isLt
    simp [initialBitCode, Expression.choose, Test.lt, Number.constant, hb, bitIndex_state, hq,
      Expression.pad_value, Expression.constant, Test.eq_value, stateIndex_eq, initialBit]
  · have hnot : ¬ Fintype.card M.Q + i.val < Fintype.card M.Q := by omega
    have hlt : Fintype.card M.Q + i.val < Fintype.card M.Q + (2 * radius.value a + 1) := by omega
    simp [initialBitCode, Expression.choose, Test.lt, Number.constant, Number.add, Number.mul,
      Number.sub, windowNumber, hb, bitIndex_head, hnot, hlt, Expression.pad_value, Expression.constant,
      Test.eq_value, initialBit, Fin.ext_iff, position_zero_value]
  · have hnot : ¬ ((bitEquiv M (radius.value a)) (.inr (.inr (i, symbol)))).val < Fintype.card M.Q := by
      rw [bitIndex_cell]; omega
    have hnot' : ¬ ((bitEquiv M (radius.value a)) (.inr (.inr (i, symbol)))).val <
        Fintype.card M.Q + (2 * radius.value a + 1) := by rw [bitIndex_cell]; omega
    have hp := cellPositionNumber_address M radius bit a i symbol hb
    have hs := cellSymbolNumber_address M radius bit a i symbol hb
    simp only [initialBitCode, Expression.choose, Test.lt, Number.constant, Number.add, Number.mul,
      windowNumber, hb, hnot, hnot', decide_false, Bool.false_eq_true, ite_false]
    rw [Expression.select_ofFn_value _ _ _ a (Fintype.equivFin M.Γ symbol) hs]
    simp only [Equiv.symm_apply_apply, initialCellCode_value, hp, initialBit, coordinate]

end Lax429075Proofs.Streaming
