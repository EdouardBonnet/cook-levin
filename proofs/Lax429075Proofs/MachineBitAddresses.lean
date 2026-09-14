import Lax429075Proofs.MachineBits

namespace Lax429075Proofs.MachineCircuit

open Lax434930.MachineModels WindowMachine

noncomputable def stateIndex (M : SingleTape) (q : M.Q) : ℕ := (Fintype.equivFin M.Q q).val

noncomputable def symbolIndex (M : SingleTape) (a : M.Γ) : ℕ := (Fintype.equivFin M.Γ a).val

lemma bitIndex_state (M : SingleTape) (radius : ℕ) (q : M.Q) :
    ((bitEquiv M radius) (.inl q)).val = stateIndex M q := by
  rfl

lemma bitIndex_head (M : SingleTape) (radius : ℕ) (i : Position radius) :
    ((bitEquiv M radius) (.inr (.inl i))).val = Fintype.card M.Q + i.val := by
  rfl

lemma bitIndex_cell (M : SingleTape) (radius : ℕ) (i : Position radius) (a : M.Γ) :
    ((bitEquiv M radius) (.inr (.inr (i, a)))).val =
      Fintype.card M.Q + (2 * radius + 1) + i.val * Fintype.card M.Γ + symbolIndex M a := by
  change Fintype.card M.Q + ((2 * radius + 1) +
    (symbolIndex M a + Fintype.card M.Γ * i.val)) = _
  ring

lemma alphabet_positive (M : SingleTape) : 0 < Fintype.card M.Γ := Fintype.card_pos

lemma states_positive (M : SingleTape) : 0 < Fintype.card M.Q := Fintype.card_pos

end Lax429075Proofs.MachineCircuit
