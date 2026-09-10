import Lax429075Proofs.Encoding
import Lax429075.FiniteWitness
import Lax429075.VerifierCorrect
import Lax429075.VerifierTime
import Lax429075.SATinNP
import Lax429075.SATEncoding

namespace Lax429075Proofs

open Lax429075 Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability
open Lax434930.PolynomialTime Lax434930.Certificates
open Lax434930.NondeterministicPolynomialTime

/--
---
conclusion: Lax429075.FiniteWitness.bounded
assumptions:
---
Restrict a satisfying assignment to the input-length prefix containing every variable.
-/
lemma finite_witness (F : Formula) :
    Satisfiable F ↔ ∃ y : Word, y.length ≤ (encodeCNF F).length ∧
      eval F (assignment y) = true := by
  constructor
  · rintro ⟨ρ, hρ⟩
    let y : Word := List.ofFn (fun i : Fin (encodeCNF F).length => ρ i)
    refine ⟨y, by simp [y], ?_⟩
    have hagree (C : Clause) (hC : C ∈ F) (l : Literal) (hl : l ∈ C) :
        l.eval (assignment y) = l.eval ρ := by
      have hi := literal_index_lt F C l hC hl
      have hv : assignment y l.index = ρ l.index := by
        simp [assignment, y, hi]
      simp only [Literal.eval, hv]
    simp only [eval, List.all_eq_true, List.any_eq_true] at hρ ⊢
    intro C hC
    obtain ⟨l, hl, he⟩ := hρ C hC
    exact ⟨l, hl, (hagree C hC l hl).trans he⟩
  · rintro ⟨y, _, hy⟩
    exact ⟨assignment y, hy⟩

/--
---
conclusion: Lax429075.VerifierCorrect.correct
assumptions:
  - Lax429075.FiniteWitness.bounded
  - Lax434930.Certificates.pair_injective
---
Use the bounded assignment and the injective encoding of input-certificate pairs.
-/
lemma verifier_correct (w : Word) :
    w ∈ SAT ↔ ∃ y : Word, y.length ≤ w.length ∧ pair w y ∈ Verifier := by
  constructor
  · rintro ⟨F, rfl, hF⟩
    obtain ⟨y, hy, he⟩ := (FiniteWitness.bounded F).mp hF
    exact ⟨y, hy, F, y, rfl, he⟩
  · rintro ⟨y, _, F, z, hz, he⟩
    have hp : (w, y) = (encodeCNF F, z) := pair_injective hz
    have hw := congrArg Prod.fst hp
    exact ⟨F, hw.symm, assignment z, he⟩

/--
---
conclusion: Lax429075.SATEncoding.correct
assumptions:
  - Lax429075.EncodingCorrect.roundtrip
---
The decoder's left-inverse property makes the binary encoding injective.
-/
lemma sat_encoding (F : Formula) : encodeCNF F ∈ SAT ↔ Satisfiable F := by
  constructor
  · rintro ⟨G, hG, hsat⟩
    have h := congrArg decodeCNF hG
    rw [EncodingCorrect.roundtrip, EncodingCorrect.roundtrip] at h
    cases Option.some.inj h
    exact hsat
  · intro h
    exact ⟨F, rfl, h⟩

/--
---
conclusion: Lax429075.SATinNP.membership
assumptions:
  - Lax429075.VerifierCorrect.correct
  - Lax429075.VerifierTime.polynomial
---
Use the identity polynomial as the certificate-length bound.
-/
lemma sat_in_np : SAT ∈ NP := by
  refine ⟨Verifier, VerifierTime.polynomial, Polynomial.X, ?_⟩
  intro w
  simpa using VerifierCorrect.correct w

end Lax429075Proofs
