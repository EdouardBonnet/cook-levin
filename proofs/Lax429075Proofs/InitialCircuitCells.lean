import Lax429075Proofs.CertificateCells

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax434930.Certificates Lax429075.CNF
open Lax434930.MachineModels CircuitBuilder
open scoped Classical

def knownSymbol (M : SingleTape) (x : Word) (i : ℕ) : M.Γ :=
  (((pairedPrefix x)[i]?).map M.input).getD default

noncomputable def initialCell (M : SingleTape) (x : Word) (bound : ℕ) (j : ℤ) (a : M.Γ) : Expr :=
  if j < 0 then pad 5 (.constant (decide (default = a)))
  else if j.toNat < (pairedPrefix x).length then pad 5 (.constant (decide (knownSymbol M x j.toNat = a)))
  else if j.toNat - (pairedPrefix x).length < bound then
    certificateCell M bound (j.toNat - (pairedPrefix x).length) a
  else pad 5 (.constant (decide (default = a)))

lemma initialCell_cost (M : SingleTape) (x : Word) (bound : ℕ) (j : ℤ) (a : M.Γ) :
    (initialCell M x bound j a).cost = 11 := by
  unfold initialCell
  split_ifs <;> simp [pad_cost, Expr.cost, certificateCell_cost]

lemma initialCell_bounded (M : SingleTape) (x : Word) (bound : ℕ) (j : ℤ) (a : M.Γ) :
    (initialCell M x bound j a).Bounded (inputCount bound) := by
  unfold initialCell
  split_ifs with hneg hp hc
  · exact pad_bounded _ _ _ trivial
  · exact pad_bounded _ _ _ trivial
  · exact certificateCell_bounded _ _ _ _ hc
  · exact pad_bounded _ _ _ trivial

lemma initialCell_word (M : SingleTape) (x : Word) (bound : ℕ) (j : ℤ) (a : M.Γ)
    (ρ : Assignment) (y : Word) (hy : y.length ≤ bound)
    (hlive : ∀ i, live bound ρ i = true ↔ i < y.length)
    (hdata : ∀ i, i < y.length → y[i]? = some (ρ (dataPort i))) :
    (initialCell M x bound j a).eval ρ =
      decide ((AbsoluteTape.initial M (pair x y)).cells j = a) := by
  by_cases hj : j < 0
  · have hn : ¬ 0 ≤ j := by omega
    simp [initialCell, hj, pad_eval, Expr.eval, AbsoluteTape.initial, hn]
  · have hn : 0 ≤ j := by omega
    by_cases hp : j.toNat < (pairedPrefix x).length
    · simp [initialCell, hj, hp, pad_eval, Expr.eval, AbsoluteTape.initial, hn,
        pair_prefix, List.getElem?_append, knownSymbol]
    · by_cases hc : j.toNat - (pairedPrefix x).length < bound
      · simp only [initialCell, hj, hp, hc, if_false, if_true]
        rw [certificateCell_word M bound _ a ρ y hc hlive hdata]
        simp [AbsoluteTape.initial, hn, pair_prefix, List.getElem?_append, hp]
      · have he : y[j.toNat - (pairedPrefix x).length]? = none :=
          List.getElem?_eq_none (by omega)
        simp [initialCell, hj, hp, hc, pad_eval, Expr.eval, AbsoluteTape.initial, hn,
          pair_prefix, List.getElem?_append, he]

end Lax429075Proofs.CertificateCircuit
