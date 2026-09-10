import Lax429075Proofs.ConclusionExpressionCode

namespace Lax429075Proofs.Streaming

open CircuitBuilder Lax434930.PolynomialTime

lemma rename_agrees_bounded (e : Expr) (n : ℕ) (f g : ℕ → ℕ) (he : e.Bounded n)
    (h : ∀ i < n, f i = g i) : e.rename f = e.rename g := by
  induction e with
  | wire i => exact congrArg Expr.wire (h i he)
  | constant b => rfl
  | neg e ih => exact congrArg Expr.neg (ih he)
  | conj e f ihe ihf => exact congrArg₂ Expr.conj (ihe he.1) (ihf he.2)
  | disj e f ihe ihf => exact congrArg₂ Expr.disj (ihe he.1) (ihf he.2)

lemma rename_wires_affine {n : ℕ} (e : Expr) (base pitch : ℕ) (v : Fin n → ℕ)
    (he : e.Bounded n) (hv : ∀ i, v i = affineAddress base pitch i.val) :
    e.rename (wires v) = e.rename (affineAddress base pitch) := by
  apply rename_agrees_bounded e n _ _ he
  intro i hi
  simpa only [wires, dif_pos hi] using hv ⟨i, hi⟩

lemma compileLayer_affine {n : ℕ} (start base pitch : ℕ) (es : Fin n → Expr) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i = affineAddress base pitch i.val) :
    compileLayer start es v = compileVector start (fun i => (es i).rename (affineAddress base pitch)) := by
  unfold compileLayer
  congr 1
  funext i
  exact rename_wires_affine (es i) base pitch v (he i) hv

lemma compileVector_affine_output {n : ℕ} (start width : ℕ) (es : Fin n → Expr)
    (hw : 0 < width) (hc : ∀ i, (es i).cost = width) :
    ∀ i, (compileVector start es).outputs i = affineAddress start width i.val := by
  intro i
  have h := compileVector_uniform_output start width es hw hc i
  unfold affineAddress
  omega

def roundBase (start initialBase count width t : ℕ) : ℕ :=
  if t = 0 then initialBase else start + (t - 1) * count * width

def roundPitch (initialPitch width t : ℕ) : ℕ := if t = 0 then initialPitch else width

lemma compileRounds_affine_output {n : ℕ} (start initialBase initialPitch width t : ℕ)
    (es : Fin n → Expr) (v : Fin n → ℕ) (hw : 0 < width) (hc : ∀ i, (es i).cost = width)
    (hv : ∀ i, v i = affineAddress initialBase initialPitch i.val) :
    ∀ i, (compileRounds start es t v).outputs i =
      affineAddress (roundBase start initialBase n width t) (roundPitch initialPitch width t) i.val := by
  intro i
  cases t with
  | zero => exact hv i
  | succ t =>
    have h := compileRounds_uniform_output start width es v hw hc t i
    simp only [roundBase, roundPitch, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, affineAddress]
    omega

end Lax429075Proofs.Streaming
