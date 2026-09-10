import Lax429075.EncodingCorrect
import Mathlib.Tactic

namespace Lax429075Proofs

open Lax429075 Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime

lemma parse_nat_append (n : ℕ) (tail : Word) :
    parseNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [encodeNat, List.replicate_succ, List.cons_append, parseNat]
    simp only [encodeNat] at ih
    rw [ih]
    rfl

lemma parse_literal_append (l : Literal) (tail : Word) :
    parseLiteral (encodeLiteral l ++ tail) = some (l, tail) := by
  simp only [encodeLiteral, List.append_assoc, parseLiteral, parse_nat_append]
  rfl

lemma parse_list_append {α : Type} (enc : α → Word) (dec : Word → Option (α × Word))
    (hdec : ∀ a tail, dec (enc a ++ tail) = some (a, tail))
    (as : List α) (tail : Word) (fuel : ℕ) (hf : as.length < fuel) :
    parseList dec fuel (encodeList enc as ++ tail) = some (as, tail) := by
  induction as generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => rfl
  | cons a as ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [encodeList, List.cons_append, List.append_assoc, parseList, hdec]
      change (parseList dec fuel (encodeList enc as ++ tail)).bind
        (fun p => some (a :: p.1, p.2)) = some (a :: as, tail)
      rw [ih fuel (by simpa using hf)]
      rfl

lemma list_length_lt_encoded {α : Type} (enc : α → Word) (as : List α) :
    as.length < (encodeList enc as).length := by
  induction as with
  | nil => simp [encodeList]
  | cons a as ih =>
    simp only [encodeList, List.length_cons, List.length_append]
    omega

lemma parse_clause_append (C : Clause) (tail : Word) :
    parseClause (encodeClause C ++ tail) = some (C, tail) := by
  unfold parseClause encodeClause
  apply parse_list_append encodeLiteral parseLiteral parse_literal_append
  have := list_length_lt_encoded encodeLiteral C
  simp only [List.length_append]
  omega

/--
---
conclusion: Lax429075.EncodingCorrect.roundtrip
assumptions:
---
Decode unary indices, then literals, clauses, and the outer list.
-/
lemma encoding_roundtrip (F : Formula) : decodeCNF (encodeCNF F) = some F := by
  have h := parse_list_append encodeClause parseClause parse_clause_append F []
    (encodeCNF F).length (list_length_lt_encoded encodeClause F)
  simp only [List.append_nil] at h
  change parseList parseClause (encodeCNF F).length (encodeCNF F) = some (F, []) at h
  unfold decodeCNF
  rw [h]
  rfl

lemma member_encoding_lt {α : Type} (enc : α → Word) (as : List α) (a : α)
    (ha : a ∈ as) : (enc a).length < (encodeList enc as).length := by
  induction as with
  | nil => simp at ha
  | cons b as ih =>
    simp only [List.mem_cons] at ha
    simp only [encodeList, List.length_cons, List.length_append]
    rcases ha with rfl | ha
    · have := list_length_lt_encoded enc as
      omega
    · have := ih ha
      omega

lemma literal_index_lt (F : Formula) (C : Clause) (l : Literal)
    (hC : C ∈ F) (hl : l ∈ C) : l.index < (encodeCNF F).length := by
  have h₁ : l.index < (encodeLiteral l).length := by
    simp [encodeLiteral, encodeNat]
  have h₂ := member_encoding_lt encodeLiteral C l hl
  have h₃ := member_encoding_lt encodeClause F C hC
  exact (h₁.trans h₂).trans h₃

end Lax429075Proofs
