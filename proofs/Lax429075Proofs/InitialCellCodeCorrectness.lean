import Lax429075Proofs.InitialCellCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open CertificateCircuit CircuitBuilder
open scoped Classical

variable {I : Type}

lemma knownSymbol_prefix (M : SingleTape) (x : Word) (i : ℕ) (hi : i < (pairedPrefix x).length) :
    knownSymbol M x i = M.input (prefixBit x i) := by
  have hp := prefixBit_correct x i hi
  cases h : (pairedPrefix x)[i]? with
  | none =>
    have hn := List.getElem?_eq_none_iff.mp h
    omega
  | some b =>
    have hb : b = prefixBit x i := by simpa only [h, Option.getD_some] using hp
    simp [knownSymbol, h, hb]

lemma knownSymbol_test (M : SingleTape) (input : I) (i : Number I) (symbol : M.Γ) (a : I → Word)
    (hi : i.value a < (pairedPrefix (a input)).length) :
    (Test.choose (knownBitCode input i) (.constant (decide (M.input true = symbol)))
      (.constant (decide (M.input false = symbol)))).value a =
      decide (knownSymbol M (a input) (i.value a) = symbol) := by
  rw [knownSymbol_prefix M _ _ hi]
  simp only [Test.choose, knownBitCode_value, Test.constant]
  cases prefixBit (a input) (i.value a) <;> rfl

lemma initialCellCode_value (M : SingleTape) (input : I) (bound radius position : Number I)
    (symbol : M.Γ) (a : I → Word) :
    (initialCellCode M input bound radius position symbol).value a =
      initialCell M (a input) (bound.value a) ((position.value a : ℤ) - radius.value a) symbol := by
  have hj : ((position.value a : ℤ) - radius.value a).toNat = position.value a - radius.value a := by omega
  have hneg : ((position.value a : ℤ) - radius.value a < 0) ↔ position.value a < radius.value a := by omega
  have hknown := knownSymbol_test M input (position.sub radius) symbol a
  simp only [Number.sub, pairedPrefix_length] at hknown
  simp only [initialCellCode, Expression.choose, Test.lt, Number.sub, Number.add, Number.mul,
    Number.constant, Number.length, decide_eq_true_eq, Expression.pad_value, Expression.constant,
    Test.constant, certificateCellCode_value, initialCell, hj, hneg, pairedPrefix_length]
  split_ifs with hpos hp hc
  · rfl
  · exact congrArg (fun b => CircuitBuilder.pad 5 (Expr.constant b)) (hknown hp)
  · rfl
  · rfl

end Lax429075Proofs.Streaming
