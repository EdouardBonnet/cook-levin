import Lax429075Proofs.TransitionExpressionCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder CertificateCircuit

variable {I : Type}

def bitCountNumber (M : SingleTape) (radius : Number I) : Number I :=
  (Number.constant (Fintype.card M.Q)).add
    ((windowNumber radius).add ((windowNumber radius).mul (.constant (Fintype.card M.Γ))))

def blockSizeNumber (M : SingleTape) (radius : Number I) : Number I :=
  ((Number.constant 5).mul (caseCountNumber M radius)).add (.constant 1)

lemma blockSizeNumber_value (M : SingleTape) (radius : Number I) (a : I → Word) :
    (blockSizeNumber M radius).value a = blockSize M (radius.value a) := by
  simp [blockSizeNumber, Number.add, Number.mul, Number.constant, caseCountNumber, windowNumber,
    blockSize, Nat.mul_assoc]

def manyCode (start n width : Number I) (term : Expression (Option I)) : Code I :=
  Code.loop n (term.run ((start.rename some).add ((Number.length none).mul (width.rename some))))

lemma manyCode_correct (start n width : Number I) (term : Expression (Option I)) (a : I → Word)
    (hc : ∀ i < n.value a, (term.value (extend a (List.replicate i true))).cost = width.value a) :
    (manyCode start n width term).eval a =
      gatesWord (start.value a) (compileMany (start.value a) ((List.range (n.value a)).map
        (fun i => term.value (extend a (List.replicate i true))))).gates := by
  rw [compileMany_range_word (start.value a) (width.value a) (n.value a) _ hc]
  simp [manyCode, Code.eval_loop, Expression.eval_run, Number.add, Number.mul, Number.length,
    Number.rename, extend_some, extend]

noncomputable def initialVectorCode (M : SingleTape) (input : I) (bound radius start : Number I) : Code I :=
  manyCode start (bitCountNumber M radius) (.constant 11)
    (initialBitCode M (some input) (bound.rename some) (radius.rename some) (.length none))

lemma initialVectorCode_correct (M : SingleTape) (input : I) (bound radius start : Number I) (a : I → Word) :
    (initialVectorCode M input bound radius start).eval a =
      gatesWord (start.value a) (compileVector (start.value a)
        (initialExpressions M (a input) (bound.value a) (radius.value a))).gates := by
  rw [initialVectorCode, manyCode_correct _ _ _ _ a (fun i _ => initialBitCode_cost M _ _ _ _ _)]
  have he : (List.range (bitCount M (radius.value a))).map (fun i =>
      (initialBitCode M (some input) (bound.rename some) (radius.rename some) (Number.length none)).value
        (extend a (List.replicate i true))) = List.ofFn (initialExpressions M (a input) (bound.value a) (radius.value a)) := by
    apply range_map_ofFn
    intro i
    exact initialBitCode_value M (some input) (bound.rename some) (radius.rename some) (Number.length none)
      (extend a (List.replicate i.val true)) ((bitEquiv M (radius.value a)).symm i)
      (by
        simp only [Number.length, Number.rename, extend_some, extend, Option.elim_none, List.length_replicate]
        exact congrArg Fin.val ((bitEquiv M (radius.value a)).apply_symm_apply i).symm)
  change gatesWord _ (compileMany _ _).gates = gatesWord _ (compileMany _ _).gates
  rw [show (bitCountNumber M radius).value a = bitCount M (radius.value a) from rfl, he]

noncomputable def stepVectorCode (M : SingleTape) (radius base pitch start : Number I) : Code I :=
  manyCode start (bitCountNumber M radius) (blockSizeNumber M radius)
    (stepCode M (radius.rename some) (base.rename some) (pitch.rename some) (.length none))

lemma stepVectorCode_correct (M : SingleTape) (radius base pitch start : Number I) (a : I → Word) :
    (stepVectorCode M radius base pitch start).eval a = gatesWord (start.value a)
      (compileVector (start.value a) (fun i => (stepExpressions M (radius.value a) i).rename
        (affineAddress (base.value a) (pitch.value a)))).gates := by
  rw [stepVectorCode, manyCode_correct _ _ _ _ a (by
    intro i hi
    simpa only [Number.rename, extend_some, blockSizeNumber_value] using
      stepCode_cost M (radius.rename some) (base.rename some) (pitch.rename some) (Number.length none)
        (extend a (List.replicate i true)))]
  have he : (List.range (bitCount M (radius.value a))).map (fun i =>
      (stepCode M (radius.rename some) (base.rename some) (pitch.rename some) (Number.length none)).value
        (extend a (List.replicate i true))) = List.ofFn (fun i => (stepExpressions M (radius.value a) i).rename
          (affineAddress (base.value a) (pitch.value a))) := by
    apply range_map_ofFn
    intro i
    exact stepCode_value M (radius.rename some) (base.rename some) (pitch.rename some) (Number.length none)
      (extend a (List.replicate i.val true)) ((bitEquiv M (radius.value a)).symm i)
      (by
        simp only [Number.length, Number.rename, extend_some, extend, Option.elim_none, List.length_replicate]
        exact congrArg Fin.val ((bitEquiv M (radius.value a)).apply_symm_apply i).symm)
  change gatesWord _ (compileMany _ _).gates = gatesWord _ (compileMany _ _).gates
  rw [show (bitCountNumber M radius).value a = bitCount M (radius.value a) from rfl, he]

end Lax429075Proofs.Streaming
