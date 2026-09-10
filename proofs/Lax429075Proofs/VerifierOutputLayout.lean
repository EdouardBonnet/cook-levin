import Lax429075Proofs.RoundOutputCode
import Lax429075Proofs.CircuitSizeBounds

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit CircuitBuilder CertificateCircuit

variable {I : Type}

def inputCountNumber (bound : Number I) : Number I :=
  ((Number.constant 2).mul bound).add (.constant 1)

def simulationStartNumber (M : SingleTape) (bound radius : Number I) : Number I :=
  (inputCountNumber bound).add ((bitCountNumber M radius).mul (.constant 11))

def conclusionStartNumber (M : SingleTape) (bound radius : Number I) : Number I :=
  roundStartNumber (simulationStartNumber M bound radius)
    (bitCountNumber M radius) (blockSizeNumber M radius) radius

def finalBaseNumber (M : SingleTape) (bound radius : Number I) : Number I :=
  roundBaseNumber (simulationStartNumber M bound radius) (inputCountNumber bound)
    (bitCountNumber M radius) (blockSizeNumber M radius) radius

def finalPitchNumber (M : SingleTape) (radius : Number I) : Number I :=
  roundPitchNumber (.constant 11) (blockSizeNumber M radius) radius

lemma inputCountNumber_value (bound : Number I) (a : I → Word) :
    (inputCountNumber bound).value a = inputCount (bound.value a) := rfl

lemma simulationStartNumber_value (M : SingleTape) (bound radius : Number I) (a : I → Word) (x : Word) :
    (simulationStartNumber M bound radius).value a =
      VerifierCircuit.simulationStart M x (bound.value a) (radius.value a) := by
  simp [simulationStartNumber, Number.add, Number.mul, Number.constant,
    inputCountNumber_value, bitCountNumber_value, VerifierCircuit.simulationStart,
    VerifierCircuit.preparation_size]

lemma conclusionStartNumber_value (M : SingleTape) (bound radius : Number I) (a : I → Word) (x : Word) :
    (conclusionStartNumber M bound radius).value a =
      VerifierCircuit.conclusionStart M x (bound.value a) (radius.value a) := by
  rw [conclusionStartNumber, roundStartNumber_value, simulationStartNumber_value M bound radius a x,
    bitCountNumber_value, blockSizeNumber_value, VerifierCircuit.conclusionStart,
    VerifierCircuit.simulation_size]

lemma preparation_affine_output (M : SingleTape) (x : Word) (bound radius : ℕ) :
    ∀ i, (VerifierCircuit.preparation M x bound radius).outputs i =
      affineAddress (inputCount bound) 11 i.val :=
  compileVector_affine_output (inputCount bound) 11 (initialExpressions M x bound radius)
    (by omega) (fun _ => initialBit_cost M x bound radius _)

lemma simulation_affine_output (M : SingleTape) (bound radius : Number I) (a : I → Word) (x : Word) :
    ∀ i, (VerifierCircuit.simulation M x (bound.value a) (radius.value a)).outputs i =
      affineAddress ((finalBaseNumber M bound radius).value a)
        ((finalPitchNumber M radius).value a) i.val := by
  simp only [finalBaseNumber, finalPitchNumber, roundBaseNumber_value, roundPitchNumber_value,
    simulationStartNumber_value M bound radius a x, inputCountNumber_value,
    bitCountNumber_value, blockSizeNumber_value, Number.constant]
  exact compileRounds_affine_output _ _ _ _ _ _ _ (by simp [blockSize])
    (stepExpressions_cost M (radius.value a))
    (preparation_affine_output M x (bound.value a) (radius.value a))

noncomputable def verifierConclusionCode (M : SingleTape) (bound radius : Number I) : Expression I :=
  conclusionCode M bound (finalBaseNumber M bound radius) (finalPitchNumber M radius)

lemma verifierConclusionCode_value (M : SingleTape) (bound radius : Number I) (a : I → Word) (x : Word) :
    (verifierConclusionCode M bound radius).value a =
      conclusionExpr M (bound.value a) (radius.value a)
        (VerifierCircuit.simulation M x (bound.value a) (radius.value a)).outputs := by
  rw [verifierConclusionCode, conclusionCode_value M bound _ _ (radius.value a), conclusionExpr,
    rename_wires_affine _ _ _ _ (acceptanceExpr_bounded M (radius.value a))
      (simulation_affine_output M bound radius a x)]

end Lax429075Proofs.Streaming
