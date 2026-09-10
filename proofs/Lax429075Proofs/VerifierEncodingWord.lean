import Lax429075Proofs.VerifierOutputLayout

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open Lax429075.CNF Lax429075.Circuits Lax429075.Encoding Lax429075.Tseitin
open CircuitBuilder CertificateCircuit

lemma circuit_encoding_word (C : Circuit) :
    encodeCNF (Lax429075.Tseitin.encode C) =
      CNFOutput.segment [[positive C.output]] ++ gatesWord 0 C.gates ++ [false] := by
  rw [← CNFOutput.segment_encode]
  simp [Lax429075.Tseitin.encode, CNFOutput.segment, gatesWord, List.flatMap_assoc]

lemma gatesWord_inputs (start count : ℕ) : gatesWord start (List.replicate count Gate.input) = [] := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    change gatesWord start ([Gate.input] ++ List.replicate count Gate.input) = []
    rw [gatesWord_append, gatesWord_singleton]
    simpa [gateClauses, CNFOutput.segment] using ih (start + 1)

lemma verifier_encoding_word (M : SingleTape) (x : Word) (bound radius : ℕ) :
    encodeCNF (Lax429075.Tseitin.encode (VerifierCircuit.circuit M x bound radius)) =
      CNFOutput.segment [[positive (VerifierCircuit.conclusion M x bound radius).output]] ++
      (gatesWord (inputCount bound) (VerifierCircuit.preparation M x bound radius).gates ++
      (gatesWord (VerifierCircuit.simulationStart M x bound radius) (VerifierCircuit.simulation M x bound radius).gates ++
      (gatesWord (VerifierCircuit.conclusionStart M x bound radius) (VerifierCircuit.conclusion M x bound radius).gates ++
      [false]))) := by
  rw [circuit_encoding_word]
  simp only [VerifierCircuit.circuit, assemble, gatesWord_append, gatesWord_inputs,
    List.length_replicate, Nat.zero_add, List.nil_append, VerifierCircuit.body,
    gatesWord_append, List.append_assoc, VerifierCircuit.simulationStart, VerifierCircuit.conclusionStart]

end Lax429075Proofs.Streaming
