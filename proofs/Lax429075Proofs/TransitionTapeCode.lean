import Lax429075Proofs.TransitionGuardCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder
open scoped Classical

variable {I : Type}

def unchangedCode (base pitch bit : Number I) : Expression I :=
  let e := Expression.wire (wireNumber base pitch bit)
  Expression.conj e e

lemma unchangedCode_cost (base pitch bit : Number I) (a : I → Word) :
    ((unchangedCode base pitch bit).value a).cost = 1 := rfl

lemma unchangedCode_value (base pitch bit : Number I) (a : I → Word) :
    (unchangedCode base pitch bit).value a =
      Expr.conj (.wire (affineAddress (base.value a) (pitch.value a) (bit.value a)))
        (.wire (affineAddress (base.value a) (pitch.value a) (bit.value a))) := rfl

noncomputable def tapeResultCode (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) : Expression I :=
  match M.transition q symbol with
  | some (_, .write written) =>
    Expression.choose (Test.eq (cellPositionNumber M radius bit) position)
      (.constant (Test.eq (.constant (symbolIndex M written)) (cellSymbolNumber M radius bit)))
      (unchangedCode base pitch bit)
  | _ => unchangedCode base pitch bit

lemma tapeResultCode_cost (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word) :
    ((tapeResultCode M radius position base pitch bit q symbol).value a).cost = 1 := by
  cases ht : M.transition q symbol with
  | none => simpa [tapeResultCode, ht] using unchangedCode_cost base pitch bit a
  | some p =>
    obtain ⟨q', op⟩ := p
    cases op with
    | move dir => cases dir <;> simp [tapeResultCode, ht, unchangedCode_cost]
    | write s =>
      simp only [tapeResultCode, ht, Expression.choose]
      split_ifs <;> first | rfl | exact unchangedCode_cost _ _ _ _

lemma tapeResultCode_value (M : SingleTape) (radius position base pitch bit : Number I)
    (q : M.Q) (symbol : M.Γ) (a : I → Word)
    (i j : Position (radius.value a)) (outputSymbol : M.Γ)
    (hi : position.value a = i.val)
    (hb : bit.value a = ((bitEquiv M (radius.value a)) (.inr (.inr (j, outputSymbol)))).val) :
    (tapeResultCode M radius position base pitch bit q symbol).value a =
      (caseResult M (radius.value a) (.inr (.inr (j, outputSymbol))) q i symbol).rename
        (affineAddress (base.value a) (pitch.value a)) := by
  have hp := cellPositionNumber_address M radius bit a j outputSymbol hb
  have hs := cellSymbolNumber_address M radius bit a j outputSymbol hb
  cases ht : M.transition q symbol with
  | none => simp [tapeResultCode, ht, caseResult, unchangedCode_value, wire, Expr.rename, hb]
  | some p =>
    obtain ⟨q', op⟩ := p
    cases op with
    | move dir => cases dir <;> simp [tapeResultCode, ht, caseResult, unchangedCode_value, wire, Expr.rename, hb]
    | write s =>
      simp only [tapeResultCode, ht, Expression.choose, Test.eq_value, hp, hi, decide_eq_true_eq,
        Expression.constant, Number.constant, hs, symbolIndex_eq, unchangedCode_value, hb, caseResult]
      have he : j.val = i.val ↔ j = i := Fin.val_inj
      simp only [he]
      split_ifs <;> rfl

end Lax429075Proofs.Streaming
