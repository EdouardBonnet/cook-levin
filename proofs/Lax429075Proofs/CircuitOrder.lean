import Lax429075Proofs.CircuitExpressions

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

lemma compile_ordered (start : ℕ) (e : Expr) (h : e.Bounded start) :
    Ordered start (compile start e).gates := by
  induction e generalizing start with
  | wire i => simp [compile, Ordered]
  | constant b => exact ordered_singleton start _ (by simp [Gate.inputs])
  | neg a ih =>
    refine ordered_append start _ _ (ih start h) (ordered_singleton _ _ ?_)
    intro j hj
    have he : j = (compile start a).output := by simpa [Gate.inputs] using hj
    rw [he]
    exact compile_output start a h
  | conj a b iha ihb | disj a b iha ihb =>
    have hb := bounded_mono b h.2 (Nat.le_add_right start (compile start a).gates.length)
    refine ordered_append start _ _ (ordered_append start _ _ (iha start h.1) (ihb _ hb))
      (ordered_singleton _ _ ?_)
    intro j hj
    have he : j = (compile start a).output ∨
        j = (compile (start + (compile start a).gates.length) b).output := by
      simpa [Gate.inputs] using hj
    rcases he with rfl | rfl
    · have hh := compile_output start a h.1
      simp only [List.length_append]
      omega
    · have hh := compile_output _ b hb
      simp only [List.length_append]
      omega

end Lax429075Proofs.CircuitBuilder
