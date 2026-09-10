import Lax429075Proofs.CircuitFoldLayout
import Lax429075Proofs.OutputGates

namespace Lax429075Proofs.Streaming

open CircuitBuilder Lax434930.PolynomialTime

lemma compileMany_uniform_outputs (start width : ℕ) (es : List Expr)
    (hw : 0 < width) (hc : ∀ e ∈ es, e.cost = width) :
    (compileMany start es).outputs = (List.range es.length).map (fun i => start + (i + 1) * width - 1) := by
  apply List.ext_getElem
  · simp [compileMany_outputs_length]
  · intro i hi hj
    have hi' : i < es.length := by simpa [compileMany_outputs_length] using hi
    have h := compileMany_uniform_output start width es hw hc i hi'
    simp only [List.getElem_map, List.getElem_range]
    omega

lemma compileMany_range'_word (start width offset n : ℕ) (f : ℕ → Expr)
    (hc : ∀ i ∈ List.range' offset n, (f i).cost = width) :
    gatesWord (start + offset * width)
      (compileMany (start + offset * width) ((List.range' offset n).map f)).gates =
    (List.range' offset n).flatMap (fun i => gatesWord (start + i * width)
      (compile (start + i * width) (f i)).gates) := by
  induction n generalizing offset with
  | zero => simp [compileMany, gatesWord_nil]
  | succ n ih =>
    have hf := hc offset (by simp)
    have ht : ∀ i ∈ List.range' (offset + 1) n, (f i).cost = width := by
      intro i hi
      exact hc i (by simp only [List.range'_succ, List.mem_cons]; exact Or.inr hi)
    simp only [List.range'_succ, List.map_cons, List.flatMap_cons, compileMany, gatesWord_append]
    rw [compile_length, hf]
    have hs : start + offset * width + width = start + (offset + 1) * width := by ring
    rw [hs, ih (offset + 1) ht]

lemma compileMany_range_word (start width n : ℕ) (f : ℕ → Expr)
    (hc : ∀ i < n, (f i).cost = width) :
    gatesWord start (compileMany start ((List.range n).map f)).gates =
      (List.range n).flatMap (fun i => gatesWord (start + i * width)
        (compile (start + i * width) (f i)).gates) := by
  have h := compileMany_range'_word start width 0 n f (by
    intro i hi
    exact hc i (by simpa using hi))
  simpa [← List.range_eq_range'] using h

end Lax429075Proofs.Streaming
