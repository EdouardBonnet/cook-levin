import Lax429075Proofs.VerifierEncodingWord

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open Lax429075.CNF Lax429075.Circuits Lax429075.Encoding Lax429075.Tseitin
open CircuitBuilder CertificateCircuit

variable {I : Type}

noncomputable def verifierCode (M : SingleTape) (input : I) (bound radius : Number I) : Code I :=
  let conclusion := verifierConclusionCode M bound radius
  let lastStart := conclusionStartNumber M bound radius
  (Code.segment [[(conclusion.outputAt lastStart, Test.constant true)]]).append
    ((initialVectorCode M input bound radius (inputCountNumber bound)).append
      ((roundsCode M radius (simulationStartNumber M bound radius) (inputCountNumber bound) (.constant 11) radius).append
        ((conclusion.run lastStart).append (.literal [false]))))

lemma verifierCode_correct (M : SingleTape) (input : I) (bound radius : Number I) (a : I → Word) :
    (verifierCode M input bound radius).eval a =
      encodeCNF (Lax429075.Tseitin.encode
        (VerifierCircuit.circuit M (a input) (bound.value a) (radius.value a))) := by
  rw [verifier_encoding_word]
  have hr := roundsCode_correct M radius (simulationStartNumber M bound radius)
    (inputCountNumber bound) (.constant 11) radius a
    (VerifierCircuit.preparation M (a input) (bound.value a) (radius.value a)).outputs
    (preparation_affine_output M (a input) (bound.value a) (radius.value a))
  rw [simulationStartNumber_value M bound radius a (a input)] at hr
  simp only [verifierCode, code_append_eval, Code.eval_segment, List.map_cons, List.map_nil,
    LiteralCode.value, Test.constant, Expression.outputAt_value, initialVectorCode_correct,
    Expression.eval_run, inputCountNumber_value, hr,
    conclusionStartNumber_value M bound radius a (a input),
    verifierConclusionCode_value M bound radius a (a input)]
  rfl

end Lax429075Proofs.Streaming
