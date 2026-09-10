import Lax429075Proofs.CircuitAffineLayers

namespace Lax429075Proofs.Streaming

open CircuitBuilder Lax434930.PolynomialTime

lemma compileRounds_offset_word {n : ℕ} (start initialBase initialPitch width : ℕ)
    (es : Fin n → Expr) (hw : 0 < width) (hc : ∀ i, (es i).cost = width)
    (he : ∀ i, (es i).Bounded n) (remaining k : ℕ) (v : Fin n → ℕ)
    (hv : ∀ i, v i = affineAddress (roundBase start initialBase n width k)
      (roundPitch initialPitch width k) i.val) :
    gatesWord (start + k * n * width)
      (compileRounds (start + k * n * width) es remaining v).gates =
    (List.range' k remaining).flatMap (fun t => gatesWord (start + t * n * width)
      (compileVector (start + t * n * width) (fun i => (es i).rename
        (affineAddress (roundBase start initialBase n width t)
          (roundPitch initialPitch width t)))).gates) := by
  induction remaining generalizing k v with
  | zero => simp [compileRounds, gatesWord]
  | succ remaining ih =>
    have hl : (compileLayer (start + k * n * width) es v).gates.length = n * width := by
      rw [compileLayer_length, layerCost_uniform es width hc]
    have hs : start + k * n * width + n * width = start + (k + 1) * n * width := by ring
    have ho : ∀ i, (compileLayer (start + k * n * width) es v).outputs i =
        affineAddress (roundBase start initialBase n width (k + 1))
          (roundPitch initialPitch width (k + 1)) i.val := by
      intro i
      have h := compileLayer_uniform_output (start + k * n * width) width es v hw hc i
      simp only [roundBase, roundPitch, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel, affineAddress]
      omega
    simp only [compileRounds, gatesWord_append, hl, hs, List.range'_succ, List.flatMap_cons]
    rw [ih (k + 1) _ ho]
    rw [compileLayer_affine _ _ _ es v he hv]

lemma compileRounds_word {n : ℕ} (start initialBase initialPitch width t : ℕ)
    (es : Fin n → Expr) (v : Fin n → ℕ) (hw : 0 < width) (hc : ∀ i, (es i).cost = width)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i = affineAddress initialBase initialPitch i.val) :
    gatesWord start (compileRounds start es t v).gates =
      (List.range t).flatMap (fun k => gatesWord (start + k * n * width)
        (compileVector (start + k * n * width) (fun i => (es i).rename
          (affineAddress (roundBase start initialBase n width k)
            (roundPitch initialPitch width k)))).gates) := by
  simpa [roundBase, roundPitch, List.range_eq_range'] using
    compileRounds_offset_word start initialBase initialPitch width es hw hc he t 0 v hv

end Lax429075Proofs.Streaming
