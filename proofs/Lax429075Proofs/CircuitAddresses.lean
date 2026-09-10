import Lax429075Proofs.CircuitRounds

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits

lemma compile_last (start : ℕ) (e : Expr) (h : 0 < e.cost) :
    (compile start e).output + 1 = start + e.cost := by
  cases e <;> simp_all [Expr.cost, compile, compile_length] <;> omega

lemma compileMany_uniform_output (start width : ℕ) (es : List Expr)
    (hw : 0 < width) (hc : ∀ e ∈ es, e.cost = width) (i : ℕ) (hi : i < es.length) :
    (compileMany start es).outputs[i]'(by simpa [compileMany_outputs_length] using hi) + 1 =
      start + (i + 1) * width := by
  induction es generalizing start i with
  | nil => simp at hi
  | cons e es ih =>
    have he := hc e (by simp)
    have ht : ∀ a ∈ es, a.cost = width := fun a ha => hc a (by simp [ha])
    cases i with
    | zero => simpa [compileMany, he] using compile_last start e (by omega)
    | succ i =>
      have hh := ih (start + (compile start e).gates.length) ht i (by simpa using hi)
      simp only [compileMany, List.getElem_cons_succ, compile_length, he, Nat.add_mul,
        Nat.one_mul] at hh ⊢
      omega

lemma compileVector_uniform_output {n : ℕ} (start width : ℕ) (es : Fin n → Expr)
    (hw : 0 < width) (hc : ∀ i, (es i).cost = width) (i : Fin n) :
    (compileVector start es).outputs i + 1 = start + (i.val + 1) * width := by
  apply compileMany_uniform_output start width (List.ofFn es) hw
  · intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact hc j
  · simpa using i.isLt

lemma layerCost_uniform {n : ℕ} (es : Fin n → Expr) (width : ℕ)
    (hc : ∀ i, (es i).cost = width) : layerCost es = n * width := by
  simp [layerCost, hc]

lemma compileLayer_uniform_output {n : ℕ} (start width : ℕ) (es : Fin n → Expr)
    (v : Fin n → ℕ) (hw : 0 < width) (hc : ∀ i, (es i).cost = width) (i : Fin n) :
    (compileLayer start es v).outputs i + 1 = start + (i.val + 1) * width := by
  exact compileVector_uniform_output start width _ hw (by intro j; simpa [cost_rename] using hc j) i

lemma compileRounds_uniform_output {n : ℕ} (start width : ℕ) (es : Fin n → Expr)
    (v : Fin n → ℕ) (hw : 0 < width) (hc : ∀ i, (es i).cost = width) (t : ℕ) (i : Fin n) :
    (compileRounds start es (t + 1) v).outputs i + 1 =
      start + t * n * width + (i.val + 1) * width := by
  induction t generalizing start v with
  | zero => simpa [compileRounds] using compileLayer_uniform_output start width es v hw hc i
  | succ t ih =>
    have hh := ih (start + (compileLayer start es v).gates.length) (compileLayer start es v).outputs
    simpa [compileRounds, compileLayer_length, layerCost_uniform es width hc,
      Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

end Lax429075Proofs.CircuitBuilder
