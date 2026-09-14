import Lax429075Proofs.VerifierCircuit
import Lax429075Proofs.CertificateRepresentation

namespace Lax429075Proofs.VerifierCircuit

open Lax434930.PolynomialTime Lax434930.Certificates Lax429075 Lax429075.CNF Lax429075.Circuits
open Lax434930.MachineModels CircuitBuilder CertificateCircuit MachineCircuit

lemma body_value (M : SingleTape) (x : Word) (bound radius : ℕ) (ρ : Assignment) (y : Word)
    (hy : CertificateCircuit.Represents bound ρ y)
    (hs : Satisfies (inputCount bound) (body M x bound radius) ρ) :
    ρ (conclusion M x bound radius).output =
      ((prefixExpr bound).eval ρ &&
        M.accept ((WindowMachine.next M radius)^[radius] (WindowMachine.initial M radius (pair x y))).state) := by
  obtain ⟨hinit, hrun, hfinal⟩ := (body_satisfies M x bound radius ρ).mp hs
  have hi : (fun i => ρ ((preparation M x bound radius).outputs i)) =
      encode M radius (WindowMachine.initial M radius (pair x y)) := by
    funext i
    exact (compileVector_sound _ _ ρ hinit i).trans
      (initialBit_word M x bound radius _ ρ y hy.1 hy.2.1 hy.2.2)
  have ht := simulation_sound M radius (simulationStart M x bound radius) radius
    (preparation M x bound radius).outputs _ ρ hi hrun
  have ho := compile_sound (conclusionStart M x bound radius)
    (conclusionExpr M bound radius (simulation M x bound radius).outputs) ρ hfinal
  exact ho.trans (conclusionExpr_eval M bound radius _ ρ _ ht)

lemma circuit_sound (M : SingleTape) (x : Word) (bound radius : ℕ)
    (h : Circuits.Satisfiable (circuit M x bound radius)) :
    ∃ y : Word, y.length ≤ bound ∧
      M.accept ((WindowMachine.next M radius)^[radius] (WindowMachine.initial M radius (pair x y))).state = true := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨hout, hs⟩ := (assemble_check _ _ _ _ _ ρ).mp hρ
  have hf := ((body_satisfies M x bound radius ρ).mp hs).2.2
  have ho := compile_sound (conclusionStart M x bound radius)
    (conclusionExpr M bound radius (simulation M x bound radius).outputs) ρ hf
  have hp : (prefixExpr bound).eval ρ = true := by
    have he : (conclusionExpr M bound radius (simulation M x bound radius).outputs).eval ρ = true :=
      ho.symm.trans hout
    exact (Bool.and_eq_true_iff.mp he).1
  obtain ⟨y, hy⟩ := certificate_exists bound ρ ((prefixExpr_correct bound ρ).mp hp)
  refine ⟨y, hy.1, ?_⟩
  have hv := body_value M x bound radius ρ y hy hs
  rw [hout, hp] at hv
  simpa using hv.symm

lemma circuit_complete (M : SingleTape) (x : Word) (bound radius : ℕ) (y : Word)
    (hy : y.length ≤ bound)
    (haccept : M.accept ((WindowMachine.next M radius)^[radius]
      (WindowMachine.initial M radius (pair x y))).state = true) :
    Circuits.Satisfiable (circuit M x bound radius) := by
  let ρ := certificateAssignment bound y
  let σ := extendAll (inputCount bound) (body M x bound radius) ρ
  have ha := extendAll_before (inputCount bound) (body M x bound radius) ρ
  have hs := extendAll_satisfies (inputCount bound) (body M x bound radius) ρ (body_ordered M x bound radius)
  have hyσ := represents_agrees bound ρ σ y (assignment_represents bound y hy) ha
  have hp : (prefixExpr bound).eval σ = true :=
    (expr_agrees _ _ σ ρ (prefixExpr_bounded bound) ha).trans (certificateAssignment_valid bound y hy)
  refine ⟨σ, (assemble_check _ _ _ _ _ σ).mpr ⟨?_, hs⟩⟩
  rw [body_value M x bound radius σ y hyσ hs, hp, haccept]
  rfl

lemma circuit_correct (M : SingleTape) (x : Word) (bound radius : ℕ) :
    Circuits.Satisfiable (circuit M x bound radius) ↔
      ∃ y : Word, y.length ≤ bound ∧
        M.accept ((WindowMachine.next M radius)^[radius]
          (WindowMachine.initial M radius (pair x y))).state = true := by
  constructor
  · exact circuit_sound M x bound radius
  · rintro ⟨y, hy, ha⟩
    exact circuit_complete M x bound radius y hy ha

end Lax429075Proofs.VerifierCircuit
