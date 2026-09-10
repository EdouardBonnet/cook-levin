import Lax429075Proofs.CircuitOrder

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

def Satisfies (start : ℕ) (gates : List Gate) (ρ : Assignment) : Prop :=
  ∀ g i, (g, i) ∈ gates.zipIdx start → g.check ρ i = true

lemma satisfies_append (start : ℕ) (as bs : List Gate) (ρ : Assignment) :
    Satisfies start (as ++ bs) ρ ↔ Satisfies start as ρ ∧ Satisfies (start + as.length) bs ρ := by
  simp only [Satisfies, List.zipIdx_append, List.mem_append]
  constructor
  · intro h
    exact ⟨fun g i hg => h g i (Or.inl hg), fun g i hg => h g i (Or.inr (by simpa [Nat.add_comm] using hg))⟩
  · rintro ⟨ha, hb⟩ g i (hg | hg)
    · exact ha g i hg
    · exact hb g i (by simpa [Nat.add_comm] using hg)

lemma satisfies_singleton (start : ℕ) (g : Gate) (ρ : Assignment) :
    Satisfies start [g] ρ ↔ g.check ρ start = true := by
  simp [Satisfies]

lemma compile_sound (start : ℕ) (e : Expr) (ρ : Assignment)
    (h : Satisfies start (compile start e).gates ρ) :
    ρ (compile start e).output = e.eval ρ := by
  induction e generalizing start with
  | wire i => rfl
  | constant b =>
    have hh := (satisfies_singleton start (.constant b) ρ).mp h
    simpa [compile, Expr.eval, Gate.check] using hh
  | neg a ih =>
    obtain ⟨ha, hg⟩ := (satisfies_append start _ _ ρ).mp h
    have hh := (satisfies_singleton _ (.neg (compile start a).output) ρ).mp hg
    have he := ih start ha
    simpa [compile, Expr.eval, Gate.check, he] using hh
  | conj a b iha ihb | disj a b iha ihb =>
    obtain ⟨hboth, hg⟩ := (satisfies_append start _ _ ρ).mp h
    obtain ⟨ha, hb⟩ := (satisfies_append _ _ _ ρ).mp hboth
    have he₁ := iha start ha
    have he₂ := ihb _ hb
    rw [satisfies_singleton] at hg
    simpa [compile, Expr.eval, Gate.check, he₁, he₂, Nat.add_assoc] using hg

end Lax429075Proofs.CircuitBuilder
