import Lax429075Proofs.UniformGateStream

namespace Lax429075Proofs.Streaming

open CircuitBuilder Lax434930.PolynomialTime Lax429075.Circuits Lax429075.Tseitin CNFOutput

lemma gatesWord_cons (start : ℕ) (g : Gate) (gs : List Gate) :
    gatesWord start (g :: gs) = segment (gateClauses start g) ++ gatesWord (start + 1) gs := by
  simp [gatesWord]

lemma combineGates_range'_word (conjunction : Bool) (base offset n : ℕ) (f : ℕ → ℕ) :
    gatesWord (base + offset + 1)
      (combineGates conjunction (base + offset) ((List.range' offset n).map f)) =
    (List.range' offset n).flatMap (fun i => segment
      (gateClauses (base + i + 1) (foldGate conjunction (f i) (base + i)))) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, List.flatMap_cons, combineGates, gatesWord_cons]
    simpa only [Nat.add_assoc] using congrArg
      (fun w => segment (gateClauses (base + offset + 1) (foldGate conjunction (f offset) (base + offset))) ++ w)
      (ih (offset + 1))

lemma combineGates_range_word (conjunction : Bool) (base n : ℕ) (f : ℕ → ℕ) :
    gatesWord (base + 1) (combineGates conjunction base ((List.range n).map f)) =
      (List.range n).flatMap (fun i => segment
        (gateClauses (base + i + 1) (foldGate conjunction (f i) (base + i)))) := by
  simpa [← List.range_eq_range'] using combineGates_range'_word conjunction base 0 n f

lemma reverse_uniform_outputs (start width n : ℕ) :
    ((List.range n).map (fun i => start + (i + 1) * width - 1)).reverse =
      (List.range n).map (fun i => start + (n - i) * width - 1) := by
  rw [← List.map_reverse]
  have hr : (List.range n).reverse = (List.range n).map (n - 1 - ·) := by
    simpa [← List.range_eq_range'] using (List.reverse_range' (s := 0) (n := n))
  rw [hr, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have he : n - 1 - i + 1 = n - i := by omega
  simpa only [Function.comp_def, he]

lemma uniform_sum_cost (n width : ℕ) (f : ℕ → Expr) (hc : ∀ i < n, (f i).cost = width) :
    (((List.range n).map f).map Expr.cost).sum = n * width := by
  have h : ((List.range n).map f).map Expr.cost = List.replicate n width := by
    rw [List.map_map]
    have he : (List.range n).map (Expr.cost ∘ f) = (List.range n).map (fun _ => width) := by
      apply List.map_congr_left
      intro i hi
      exact hc i (List.mem_range.mp hi)
    simpa using he
  rw [h]
  simp

lemma compile_fold_uniform_word (conjunction : Bool) (start width n : ℕ) (f : ℕ → Expr)
    (hw : 0 < width) (hc : ∀ i < n, (f i).cost = width) :
    gatesWord start (compile start (foldExpr conjunction ((List.range n).map f))).gates =
      (List.range n).flatMap (fun i => gatesWord (start + i * width) (compile (start + i * width) (f i)).gates) ++
      (segment (gateClauses (start + n * width) (.constant conjunction)) ++
        (List.range n).flatMap (fun i => segment
          (gateClauses (start + n * width + i + 1)
            (foldGate conjunction (start + (n - i) * width - 1) (start + n * width + i))))) := by
  have hc' : ∀ e ∈ (List.range n).map f, e.cost = width := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact hc i (List.mem_range.mp hi)
  rw [compile_fold_gates, gatesWord_append, gatesWord_cons,
    compileMany_range_word start width n f hc, compileMany_length, uniform_sum_cost n width f hc,
    compileMany_uniform_outputs start width _ hw hc']
  simp only [List.length_map, List.length_range]
  rw [reverse_uniform_outputs, combineGates_range_word]

end Lax429075Proofs.Streaming
