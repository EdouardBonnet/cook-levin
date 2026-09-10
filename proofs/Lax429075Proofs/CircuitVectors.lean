import Lax429075Proofs.CircuitBlocks

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

structure VectorBlock (n : ℕ) where
  gates : List Gate
  outputs : Fin n → ℕ

def compileVector {n : ℕ} (start : ℕ) (es : Fin n → Expr) : VectorBlock n :=
  let b := compileMany start (List.ofFn es)
  ⟨b.gates, fun i => b.outputs[i.val]'(by simp [b, compileMany_outputs_length])⟩

lemma compileVector_ordered {n : ℕ} (start : ℕ) (es : Fin n → Expr)
    (h : ∀ i, (es i).Bounded start) : Ordered start (compileVector start es).gates := by
  apply compileMany_ordered
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact h i

lemma compileVector_output {n : ℕ} (start : ℕ) (es : Fin n → Expr)
    (h : ∀ i, (es i).Bounded start) (i : Fin n) :
    (compileVector start es).outputs i < start + (compileVector start es).gates.length := by
  apply compileMany_outputs_bound
  · intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact h j
  · exact List.getElem_mem _

lemma compileVector_sound {n : ℕ} (start : ℕ) (es : Fin n → Expr) (ρ : Assignment)
    (h : Satisfies start (compileVector start es).gates ρ) (i : Fin n) :
    ρ ((compileVector start es).outputs i) = (es i).eval ρ := by
  have he := compileMany_sound start (List.ofFn es) ρ h
  have hi := congrArg (fun xs : List Bool => xs[i.val]?) he
  simpa [compileVector, List.getElem?_eq_getElem, compileMany_outputs_length] using hi

def wires {n : ℕ} (v : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then v ⟨i, h⟩ else 0

def values {n : ℕ} (v : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then v ⟨i, h⟩ else false

lemma renamed_eval {n : ℕ} (e : Expr) (v : Fin n → ℕ) (ρ : Assignment) (h : e.Bounded n) :
    (e.rename (wires v)).eval ρ = e.eval (values (fun i => ρ (v i))) := by
  rw [eval_rename]
  apply expr_agrees e n _ _ h
  intro j hj
  simp [wires, values, hj]

def compileLayer {n : ℕ} (start : ℕ) (es : Fin n → Expr) (v : Fin n → ℕ) : VectorBlock n :=
  compileVector start (fun i => (es i).rename (wires v))

def evaluateLayer {n : ℕ} (es : Fin n → Expr) (v : Fin n → Bool) : Fin n → Bool :=
  fun i => (es i).eval (values v)

lemma compileLayer_bounded {n : ℕ} (start : ℕ) (es : Fin n → Expr) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i < start) (i : Fin n) :
    ((es i).rename (wires v)).Bounded start := by
  apply bounded_rename _ _ _ _ (he i)
  intro j hj
  simpa [wires, hj] using hv ⟨j, hj⟩

lemma compileLayer_sound {n : ℕ} (start : ℕ) (es : Fin n → Expr) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (ρ : Assignment)
    (h : Satisfies start (compileLayer start es v).gates ρ) :
    (fun i => ρ ((compileLayer start es v).outputs i)) = evaluateLayer es (fun i => ρ (v i)) := by
  funext i
  exact (compileVector_sound start _ ρ h i).trans (renamed_eval (es i) v ρ (he i))

def layerCost {n : ℕ} (es : Fin n → Expr) : ℕ := (List.ofFn fun i => (es i).cost).sum

lemma compileLayer_length {n : ℕ} (start : ℕ) (es : Fin n → Expr) (v : Fin n → ℕ) :
    (compileLayer start es v).gates.length = layerCost es := by
  simp [compileLayer, compileVector, compileMany_length, List.map_ofFn, Function.comp_def,
    cost_rename, layerCost]

end Lax429075Proofs.CircuitBuilder
