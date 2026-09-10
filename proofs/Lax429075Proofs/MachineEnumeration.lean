import Lax429075Proofs.MachineBitAddresses

namespace Lax429075Proofs.MachineCircuit

open Lax554803.MachineModels WindowMachine

noncomputable def enumeration (A : Type) [Fintype A] : Fin (Fintype.card A) → A := by
  classical
  exact fun i => (Finset.univ.toList : List A)[i.val]'(by simpa using i.isLt)

lemma enumeration_list (A : Type) [Fintype A] :
    List.ofFn (enumeration A) = (Finset.univ : Finset A).toList := by
  classical
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [enumeration]

lemma ofFn_product {A : Type} {m n : ℕ} (f : Fin m → Fin n → A) :
    List.ofFn (fun i : Fin (m * n) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) =
      (List.ofFn (fun i : Fin m => List.ofFn (f i))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val * n + j.val < m * n := by
    calc
      i.val * n + j.val < (i.val + 1) * n := by nlinarith [j.isLt]
      _ ≤ m * n := Nat.mul_le_mul_right n i.isLt
  have h : (⟨i.val * n + j.val, hij⟩ : Fin (m * n)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [h, Equiv.symm_apply_apply]

noncomputable def caseAt (M : SingleTape) (radius : ℕ)
    (i : Fin (Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ)) :
    M.Q × Position radius × M.Γ :=
  let p := finProdFinEquiv.symm i
  let q := finProdFinEquiv.symm p.1
  (enumeration M.Q q.1, q.2, enumeration M.Γ p.2)

lemma casesList_enumeration (M : SingleTape) (radius : ℕ) :
    casesList M radius = List.ofFn (caseAt M radius) := by
  classical
  unfold caseAt
  rw [ofFn_product (fun p : Fin (Fintype.card M.Q * (2 * radius + 1)) =>
    fun a : Fin (Fintype.card M.Γ) =>
      (enumeration M.Q (finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, enumeration M.Γ a))]
  rw [ofFn_product (fun q : Fin (Fintype.card M.Q) => fun i : Fin (2 * radius + 1) =>
    List.ofFn (fun a : Fin (Fintype.card M.Γ) => (enumeration M.Q q, i, enumeration M.Γ a)))]
  simp only [casesList, ← enumeration_list, List.flatMap_def, List.finRange,
    List.map_ofFn, Function.comp_def, List.flatten_flatten]

end Lax429075Proofs.MachineCircuit
