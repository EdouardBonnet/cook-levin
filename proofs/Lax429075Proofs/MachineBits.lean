import Lax429075Proofs.BoundedVerifier
import Lax429075Proofs.CircuitVectors

namespace Lax429075Proofs.MachineCircuit

open Turing Lax434930.MachineModels Lax434930.PolynomialTime
open WindowMachine CircuitBuilder

abbrev Bit (M : SingleTape) (radius : ℕ) := M.Q ⊕ (Position radius ⊕ (Position radius × M.Γ))

def bitCount (M : SingleTape) (radius : ℕ) : ℕ :=
  Fintype.card M.Q + ((2 * radius + 1) + (2 * radius + 1) * Fintype.card M.Γ)

noncomputable def bitEquiv (M : SingleTape) (radius : ℕ) : Bit M radius ≃ Fin (bitCount M radius) :=
  (Equiv.sumCongr (Fintype.equivFin M.Q)
    ((Equiv.sumCongr (Equiv.refl (Position radius))
      ((Equiv.prodCongr (Equiv.refl (Position radius)) (Fintype.equivFin M.Γ)).trans finProdFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

noncomputable def bitValue (M : SingleTape) (radius : ℕ) (c : Cfg M radius) : Bit M radius → Bool := by
  classical
  exact fun b => match b with
    | .inl q => decide (c.state = q)
    | .inr (.inl i) => decide (c.head = i)
    | .inr (.inr (i, a)) => decide (c.cells i = a)

noncomputable def encode (M : SingleTape) (radius : ℕ) (c : Cfg M radius) : Fin (bitCount M radius) → Bool :=
  fun i => bitValue M radius c ((bitEquiv M radius).symm i)

noncomputable def wire (M : SingleTape) (radius : ℕ) (b : Bit M radius) : Expr :=
  .wire ((bitEquiv M radius) b).val

lemma wire_bounded (M : SingleTape) (radius : ℕ) (b : Bit M radius) :
    (wire M radius b).Bounded (bitCount M radius) := ((bitEquiv M radius) b).isLt

lemma wire_eval (M : SingleTape) (radius : ℕ) (b : Bit M radius) (c : Cfg M radius) :
    (wire M radius b).eval (values (encode M radius c)) = bitValue M radius c b := by
  simp [wire, Expr.eval, values, encode]

noncomputable def casesList (M : SingleTape) (radius : ℕ) : List (M.Q × Position radius × M.Γ) :=
  (Finset.univ : Finset M.Q).toList.flatMap fun q =>
    (List.finRange (2 * radius + 1)).flatMap fun i =>
      (Finset.univ : Finset M.Γ).toList.map fun a => (q, i, a)

lemma mem_casesList (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ) :
    (q, i, a) ∈ casesList M radius := by
  classical
  simp [casesList]

noncomputable def guard (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ) : Expr :=
  .conj (wire M radius (.inl q))
    (.conj (wire M radius (.inr (.inl i))) (wire M radius (.inr (.inr (i, a)))))

lemma guard_eval (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ)
    (c : Cfg M radius) :
    (guard M radius q i a).eval (values (encode M radius c)) =
      @decide (c.state = q ∧ c.head = i ∧ c.cells i = a) (Classical.propDecidable _) := by
  classical
  simp [guard, Expr.eval, wire_eval, bitValue, Bool.decide_and]

lemma guard_bounded (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ) :
    (guard M radius q i a).Bounded (bitCount M radius) :=
  ⟨wire_bounded _ _ _, wire_bounded _ _ _, wire_bounded _ _ _⟩

end Lax429075Proofs.MachineCircuit
