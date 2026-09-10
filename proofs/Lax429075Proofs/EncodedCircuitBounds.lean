import Lax429075Proofs.Encoding
import Lax429075.Tseitin

namespace Lax429075Proofs

open Lax429075 Lax429075.CNF Lax429075.Circuits Lax429075.Encoding Lax429075.Tseitin

lemma encodeList_bound {α : Type} (enc : α → Lax434930.PolynomialTime.Word) (xs : List α)
    (bound : ℕ) (h : ∀ a ∈ xs, (enc a).length ≤ bound) :
    (encodeList enc xs).length ≤ xs.length * (bound + 1) + 1 := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih =>
    have ha := h a (by simp)
    have hs := ih (fun b hb => h b (by simp [hb]))
    simp only [encodeList, List.length_cons, List.length_append, Nat.succ_mul]
    omega

lemma gate_clauses_length (i : ℕ) (g : Gate) : (gateClauses i g).length ≤ 3 := by
  cases g <;> simp [gateClauses]

lemma gate_clause_length (i : ℕ) (g : Gate) (C : Clause) (hC : C ∈ gateClauses i g) : C.length ≤ 3 := by
  cases g <;> simp_all [gateClauses] <;> aesop

lemma gate_literal_index (i : ℕ) (g : Gate) (C : Clause) (l : Literal)
    (hC : C ∈ gateClauses i g) (hl : l ∈ C) : l.index ∈ i :: g.inputs := by
  cases g <;> simp_all [gateClauses, Gate.inputs, positive, negative] <;> aesop

lemma flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β) (bound : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ bound) : (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hs := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

lemma tseitin_formula_length (C : Circuit) : (Tseitin.encode C).length ≤ 3 * C.gates.length + 1 := by
  have h := flatMap_length_bound C.gates.zipIdx (fun gi => gateClauses gi.2 gi.1) 3
    (fun gi _ => gate_clauses_length gi.2 gi.1)
  simpa [Tseitin.encode, Nat.mul_comm] using Nat.add_le_add_left h 1

lemma tseitin_clause_bounds (C : Circuit) (D : Clause) (hD : D ∈ Tseitin.encode C) :
    D.length ≤ 3 ∧ ∀ l ∈ D, l.index < C.gates.length := by
  simp only [Tseitin.encode, List.mem_append, List.mem_singleton, List.mem_flatMap] at hD
  rcases hD with rfl | ⟨⟨g, i⟩, hgi, hD⟩
  · refine ⟨by simp, ?_⟩
    intro l hl
    have he : l = positive C.output := by simpa using hl
    subst l
    exact C.output.isLt
  · refine ⟨gate_clause_length i g D hD, ?_⟩
    intro l hl
    have hidx := gate_literal_index i g D l hD hl
    have hi : i < C.gates.length := by simpa using List.snd_lt_of_mem_zipIdx hgi
    rcases List.mem_cons.mp hidx with he | hj
    · omega
    · exact (C.ordered g i hgi l.index hj).trans hi

lemma encoded_circuit_bound (C : Circuit) :
    (encodeCNF (Tseitin.encode C)).length ≤
      (3 * C.gates.length + 1) * (3 * C.gates.length + 11) + 1 := by
  apply (encodeList_bound encodeClause (Tseitin.encode C) (3 * C.gates.length + 10) ?_).trans
  · have h := tseitin_formula_length C
    gcongr
  · intro D hD
    obtain ⟨hsize, hindex⟩ := tseitin_clause_bounds C D hD
    have h := encodeList_bound encodeLiteral D (C.gates.length + 2) (by
      intro l hl
      have hi := hindex l hl
      simp [encodeLiteral, encodeNat]
      omega)
    change (encodeList encodeLiteral D).length ≤ _
    nlinarith

end Lax429075Proofs
