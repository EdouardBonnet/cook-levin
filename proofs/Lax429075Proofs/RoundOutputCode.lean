import Lax429075Proofs.RoundGateStream

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit CircuitBuilder

variable {I : Type}

def roundBaseNumber (start initialBase count width t : Number I) : Number I :=
  Number.choose (Test.eq t (.constant 0)) initialBase
    (start.add (((t.sub (.constant 1)).mul count).mul width))

def roundPitchNumber (initialPitch width t : Number I) : Number I :=
  Number.choose (Test.eq t (.constant 0)) initialPitch width

def roundStartNumber (start count width t : Number I) : Number I :=
  start.add ((t.mul count).mul width)

lemma roundBaseNumber_value (start initialBase count width t : Number I) (a : I → Word) :
    (roundBaseNumber start initialBase count width t).value a =
      roundBase (start.value a) (initialBase.value a) (count.value a) (width.value a) (t.value a) := by
  simp [roundBaseNumber, Number.choose, Test.eq_value, Number.constant, Number.add,
    Number.sub, Number.mul, roundBase]

lemma roundPitchNumber_value (initialPitch width t : Number I) (a : I → Word) :
    (roundPitchNumber initialPitch width t).value a =
      roundPitch (initialPitch.value a) (width.value a) (t.value a) := by
  simp [roundPitchNumber, Number.choose, Test.eq_value, Number.constant, roundPitch]

lemma roundStartNumber_value (start count width t : Number I) (a : I → Word) :
    (roundStartNumber start count width t).value a =
      start.value a + t.value a * count.value a * width.value a := rfl

lemma bitCountNumber_value (M : SingleTape) (radius : Number I) (a : I → Word) :
    (bitCountNumber M radius).value a = bitCount M (radius.value a) := rfl

lemma stepExpressions_cost (M : SingleTape) (radius : ℕ) (i : Fin (bitCount M radius)) :
    (stepExpressions M radius i).cost = blockSize M radius := by
  rw [stepExpressions, stepExpr_cost_exact, blockSize_eq]

noncomputable def roundsCode (M : SingleTape) (radius start initialBase initialPitch t : Number I) : Code I :=
  let count := (bitCountNumber M radius).rename some
  let width := (blockSizeNumber M radius).rename some
  let k := Number.length (I := Option I) none
  Code.loop t (stepVectorCode M (radius.rename some)
    (roundBaseNumber (start.rename some) (initialBase.rename some) count width k)
    (roundPitchNumber (initialPitch.rename some) width k)
    (roundStartNumber (start.rename some) count width k))

lemma roundsCode_correct (M : SingleTape) (radius start initialBase initialPitch t : Number I)
    (a : I → Word) (v : Fin (bitCount M (radius.value a)) → ℕ)
    (hv : ∀ i, v i = affineAddress (initialBase.value a) (initialPitch.value a) i.val) :
    (roundsCode M radius start initialBase initialPitch t).eval a =
      gatesWord (start.value a)
        (compileRounds (start.value a) (stepExpressions M (radius.value a)) (t.value a) v).gates := by
  rw [compileRounds_word (start.value a) (initialBase.value a) (initialPitch.value a)
    (blockSize M (radius.value a)) (t.value a) _ v (by simp [blockSize])
    (stepExpressions_cost M (radius.value a))
    (fun i => stepExpr_bounded M (radius.value a) _) hv]
  simp only [roundsCode, Code.eval_loop, stepVectorCode_correct, roundBaseNumber_value,
    roundPitchNumber_value, roundStartNumber_value, Number.rename, Number.length,
    extend_some, extend, Option.elim_none, List.length_replicate,
    bitCountNumber_value, blockSizeNumber_value]

end Lax429075Proofs.Streaming
