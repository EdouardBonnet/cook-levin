import Lax429075Proofs.CircuitExpressionLists
import Lax429075.Satisfiability

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax429075.CNF CircuitBuilder

def inputCount (bound : ℕ) : ℕ := 2 * bound + 1
def dataPort (i : ℕ) : ℕ := i + 1
def livePort (bound i : ℕ) : ℕ := bound + i + 1

def live (bound : ℕ) (ρ : Assignment) (i : ℕ) : Bool :=
  if i < bound then ρ (livePort bound i) else false

def Prefix (bound : ℕ) (ρ : Assignment) : Prop :=
  ∀ i, i + 1 < bound → live bound ρ (i + 1) = true → live bound ρ i = true

lemma prefix_backwards (bound : ℕ) (ρ : Assignment) (h : Prefix bound ρ)
    (i j : ℕ) (hij : i ≤ j) (hj : j < bound) (hv : live bound ρ j = true) :
    live bound ρ i = true := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact hv
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact hv
    · exact ih i (by omega) (by omega) (h j hj hv)

lemma prefix_length (bound : ℕ) (ρ : Assignment) (h : Prefix bound ρ) :
    ∃ n, n ≤ bound ∧ ∀ i, live bound ρ i = true ↔ i < n := by
  have hex : ∃ i, live bound ρ i = false := ⟨bound, by simp [live]⟩
  let n := Nat.find hex
  have hn : live bound ρ n = false := Nat.find_spec hex
  have hb : n ≤ bound := Nat.find_min' hex (by simp [live])
  refine ⟨n, hb, ?_⟩
  intro i
  constructor
  · intro hi
    have hib : i < bound := by by_contra hh; simp [live, hh] at hi
    by_contra hni
    have hf := prefix_backwards bound ρ h n i (by omega) hib hi
    rw [hn] at hf
    contradiction
  · intro hi
    have hm : ¬ live bound ρ i = false := Nat.find_min hex hi
    cases hv : live bound ρ i <;> simp_all

def prefixExpr (bound : ℕ) : Expr :=
  allExpr ((List.range (bound - 1)).map fun i =>
    .disj (.neg (.wire (livePort bound (i + 1)))) (.wire (livePort bound i)))

lemma prefixExpr_bounded (bound : ℕ) : (prefixExpr bound).Bounded (inputCount bound) := by
  apply allExpr_bounded
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hn := List.mem_range.mp hi
  change livePort bound (i + 1) < inputCount bound ∧ livePort bound i < inputCount bound
  simp only [livePort, inputCount]
  omega

lemma prefixExpr_correct (bound : ℕ) (ρ : Assignment) :
    (prefixExpr bound).eval ρ = true ↔ Prefix bound ρ := by
  simp only [prefixExpr, allExpr_eval, List.all_eq_true, List.mem_map]
  constructor
  · intro h i hi hv
    have hm : i ∈ List.range (bound - 1) := by simp; omega
    have hp := h _ ⟨i, hm, rfl⟩
    have hv' : ρ (livePort bound (i + 1)) = true := by simpa [live, hi] using hv
    simpa [Expr.eval, hv', live, show i < bound by omega] using hp
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := he
    have hn : i + 1 < bound := by have hm := List.mem_range.mp hi; omega
    cases hv : ρ (livePort bound (i + 1)) with
    | false => simp [Expr.eval, hv]
    | true =>
      have hp := h i hn (by simpa [live, hn] using hv)
      simpa [Expr.eval, hv, live, show i < bound by omega] using hp

lemma certificate_exists (bound : ℕ) (ρ : Assignment) (h : Prefix bound ρ) :
    ∃ y : Word, y.length ≤ bound ∧
      (∀ i, live bound ρ i = true ↔ i < y.length) ∧
      (∀ i, i < y.length → y[i]? = some (ρ (dataPort i))) := by
  obtain ⟨n, hn, hp⟩ := prefix_length bound ρ h
  let y := List.ofFn (fun i : Fin n => ρ (dataPort i.val))
  refine ⟨y, by simpa [y] using hn, ?_, ?_⟩
  · simpa [y] using hp
  · intro i hi
    have hin : i < n := by simpa [y] using hi
    simp [y, hin]

end Lax429075Proofs.CertificateCircuit
