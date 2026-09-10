import Lax429075Proofs.CertificateCells

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax434930.Certificates

def prefixBit (x : Word) (i : ℕ) : Bool :=
  decide (i = 2 * x.length) || (decide (i % 2 = 1) && (x[i / 2]?).getD false)

lemma pairedPrefix_length (x : Word) : (pairedPrefix x).length = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [pairedPrefix, pair, List.length_cons] at ih ⊢; omega

lemma prefixBit_correct (x : Word) (i : ℕ) (hi : i < (pairedPrefix x).length) :
    ((pairedPrefix x)[i]?).getD false = prefixBit x i := by
  induction x generalizing i with
  | nil =>
    have he : i = 0 := by simp [pairedPrefix, pair] at hi; omega
    subst i
    rfl
  | cons b x ih =>
    cases i with
    | zero => simp [pairedPrefix, pair, prefixBit]
    | succ i =>
      cases i with
      | zero =>
        have h : (1 : ℕ) ≠ 2 * (x.length + 1) := by omega
        simp [pairedPrefix, pair, prefixBit, h]
      | succ i =>
        have hi' : i < (pairedPrefix x).length := by
          simp only [pairedPrefix, pair, List.length_cons] at hi ⊢
          omega
        have h := ih i hi'
        have hm : (i + 1 + 1) % 2 = i % 2 := by omega
        have hd : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
        have he : i + 1 + 1 = 2 * (x.length + 1) ↔ i = 2 * x.length := by omega
        simpa [pairedPrefix, pair, prefixBit, hm, hd, he] using h

end Lax429075Proofs.CertificateCircuit
