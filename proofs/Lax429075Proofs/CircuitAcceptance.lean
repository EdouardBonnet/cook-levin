import Lax429075Proofs.InitialCircuit

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax429075.CNF
open Lax434930.MachineModels CircuitBuilder WindowMachine
open scoped Classical

noncomputable def acceptanceExpr (M : SingleTape) (radius : ℕ) : Expr :=
  anyExpr ((Finset.univ : Finset M.Q).toList.map fun q =>
    .conj (MachineCircuit.wire M radius (.inl q)) (.constant (M.accept q)))

lemma acceptanceExpr_bounded (M : SingleTape) (radius : ℕ) :
    (acceptanceExpr M radius).Bounded (MachineCircuit.bitCount M radius) := by
  apply anyExpr_bounded
  intro e he
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
  exact ⟨MachineCircuit.wire_bounded _ _ _, trivial⟩

lemma acceptanceExpr_eval (M : SingleTape) (radius : ℕ) (c : Cfg M radius) :
    (acceptanceExpr M radius).eval (values (MachineCircuit.encode M radius c)) = M.accept c.state := by
  apply Bool.eq_iff_iff.mpr
  simp only [acceptanceExpr, anyExpr_eval, List.any_map, Function.comp_def, List.any_eq_true,
    Expr.eval, MachineCircuit.wire_eval, MachineCircuit.bitValue, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨q, _, hq, ha⟩
    simpa only [hq] using ha
  · intro h
    exact ⟨c.state, by simp, rfl, h⟩

lemma acceptanceExpr_cost (M : SingleTape) (radius : ℕ) :
    (acceptanceExpr M radius).cost = 3 * Fintype.card M.Q + 1 := by
  simp [acceptanceExpr, anyExpr_cost, List.map_map, Function.comp_def, Expr.cost,
    MachineCircuit.wire, Nat.mul_comm] <;> omega

noncomputable def conclusionExpr (M : SingleTape) (bound radius : ℕ)
    (v : Fin (MachineCircuit.bitCount M radius) → ℕ) : Expr :=
  .conj (prefixExpr bound) ((acceptanceExpr M radius).rename (wires v))

lemma conclusionExpr_bounded (M : SingleTape) (bound radius start : ℕ)
    (v : Fin (MachineCircuit.bitCount M radius) → ℕ)
    (hs : inputCount bound ≤ start) (hv : ∀ i, v i < start) :
    (conclusionExpr M bound radius v).Bounded start := by
  refine ⟨bounded_mono _ (prefixExpr_bounded bound) hs, ?_⟩
  apply bounded_rename _ _ _ _ (acceptanceExpr_bounded M radius)
  intro j hj
  simpa [wires, hj] using hv ⟨j, hj⟩

lemma conclusionExpr_eval (M : SingleTape) (bound radius : ℕ)
    (v : Fin (MachineCircuit.bitCount M radius) → ℕ) (ρ : Assignment) (c : Cfg M radius)
    (h : (fun i => ρ (v i)) = MachineCircuit.encode M radius c) :
    (conclusionExpr M bound radius v).eval ρ = ((prefixExpr bound).eval ρ && M.accept c.state) := by
  unfold conclusionExpr
  simp only [Expr.eval]
  rw [renamed_eval _ _ _ (acceptanceExpr_bounded M radius), h, acceptanceExpr_eval]

end Lax429075Proofs.CertificateCircuit
