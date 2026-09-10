import Lax429075Proofs.CircuitAssembly

namespace Lax429075Proofs.VerifierCircuit

open Lax434930.PolynomialTime Lax429075.CNF Lax429075.Circuits
open Lax554803.MachineModels CircuitBuilder CertificateCircuit MachineCircuit

noncomputable def preparation (M : SingleTape) (x : Word) (bound radius : ℕ) : VectorBlock (bitCount M radius) :=
  compileVector (inputCount bound) (initialExpressions M x bound radius)

noncomputable def simulationStart (M : SingleTape) (x : Word) (bound radius : ℕ) : ℕ :=
  inputCount bound + (preparation M x bound radius).gates.length

noncomputable def simulation (M : SingleTape) (x : Word) (bound radius : ℕ) : VectorBlock (bitCount M radius) :=
  compileRounds (simulationStart M x bound radius) (stepExpressions M radius) radius
    (preparation M x bound radius).outputs

noncomputable def conclusionStart (M : SingleTape) (x : Word) (bound radius : ℕ) : ℕ :=
  simulationStart M x bound radius + (simulation M x bound radius).gates.length

noncomputable def conclusion (M : SingleTape) (x : Word) (bound radius : ℕ) : Fragment :=
  compile (conclusionStart M x bound radius)
    (conclusionExpr M bound radius (simulation M x bound radius).outputs)

noncomputable def body (M : SingleTape) (x : Word) (bound radius : ℕ) : List Gate :=
  (preparation M x bound radius).gates ++
    ((simulation M x bound radius).gates ++ (conclusion M x bound radius).gates)

lemma preparation_ordered (M : SingleTape) (x : Word) (bound radius : ℕ) :
    Ordered (inputCount bound) (preparation M x bound radius).gates :=
  compileVector_ordered _ _ (fun i => initialBit_bounded M x bound radius _)

lemma preparation_output (M : SingleTape) (x : Word) (bound radius : ℕ) (i : Fin (bitCount M radius)) :
    (preparation M x bound radius).outputs i < simulationStart M x bound radius :=
  compileVector_output _ _ (fun i => initialBit_bounded M x bound radius _) i

lemma simulation_ordered (M : SingleTape) (x : Word) (bound radius : ℕ) :
    Ordered (simulationStart M x bound radius) (simulation M x bound radius).gates :=
  compileRounds_ordered _ _ _ _ (fun i => stepExpr_bounded M radius _) (preparation_output M x bound radius)

lemma simulation_output (M : SingleTape) (x : Word) (bound radius : ℕ) (i : Fin (bitCount M radius)) :
    (simulation M x bound radius).outputs i < conclusionStart M x bound radius :=
  compileRounds_output _ _ _ _ (fun i => stepExpr_bounded M radius _) (preparation_output M x bound radius) i

lemma conclusion_bounded (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (conclusionExpr M bound radius (simulation M x bound radius).outputs).Bounded
      (conclusionStart M x bound radius) := by
  apply conclusionExpr_bounded
  · simp only [conclusionStart, simulationStart]; omega
  · exact simulation_output M x bound radius

lemma body_ordered (M : SingleTape) (x : Word) (bound radius : ℕ) :
    Ordered (inputCount bound) (body M x bound radius) :=
  ordered_append _ _ _ (preparation_ordered M x bound radius)
    (ordered_append _ _ _ (simulation_ordered M x bound radius)
      (compile_ordered _ _ (conclusion_bounded M x bound radius)))

lemma body_output (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (conclusion M x bound radius).output < inputCount bound + (body M x bound radius).length := by
  have h := compile_output _ _ (conclusion_bounded M x bound radius)
  change (conclusion M x bound radius).output <
    conclusionStart M x bound radius + (conclusion M x bound radius).gates.length at h
  simp only [conclusionStart, simulationStart, body, List.length_append] at h ⊢
  omega

noncomputable def circuit (M : SingleTape) (x : Word) (bound radius : ℕ) : Circuit :=
  assemble (inputCount bound) (body M x bound radius) (conclusion M x bound radius).output
    (body_ordered M x bound radius) (body_output M x bound radius)

lemma body_satisfies (M : SingleTape) (x : Word) (bound radius : ℕ) (ρ : Assignment) :
    Satisfies (inputCount bound) (body M x bound radius) ρ ↔
      Satisfies (inputCount bound) (preparation M x bound radius).gates ρ ∧
      Satisfies (simulationStart M x bound radius) (simulation M x bound radius).gates ρ ∧
      Satisfies (conclusionStart M x bound radius) (conclusion M x bound radius).gates ρ := by
  simp only [body, satisfies_append]
  rfl

end Lax429075Proofs.VerifierCircuit
