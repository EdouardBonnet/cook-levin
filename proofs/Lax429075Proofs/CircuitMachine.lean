import Lax429075Proofs.VerifierOutputCode
import Lax429075Proofs.OutputMachine
import Lax429075Proofs.OutputPolynomials
import Lax429075Proofs.VerifierCompilation
import Lax429075.CircuitMachine

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax434930.Certificates Lax434930.MachineModels
open Lax429075.Encoding Turing

lemma verifier_polynomial_time (M : SingleTape) (p R : Polynomial ℕ) :
    Nonempty (TM2ComputableInPolyTime id id (fun x =>
      encodeCNF (Lax429075.Tseitin.encode
        (VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length))))) := by
  let c := verifierCode M () (Number.polynomial p (.length ())) (Number.polynomial R (.length ()))
  have he : (fun x => c.eval (fun _ => x)) = (fun x =>
      encodeCNF (Lax429075.Tseitin.encode
        (VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length)))) := by
    funext x
    simpa only [Number.polynomial_value, Number.length] using!
      verifierCode_correct M () (Number.polynomial p (.length ()))
        (Number.polynomial R (.length ())) (fun _ => x)
  have h := c.polynomial_time
  rw [he] at h
  exact h

/--
---
conclusion: Lax429075.CircuitMachine.compile
assumptions:
  - Lax434930.Certificates.pair_length
  - Lax434930.ModelEquivalence.singleTapeP_eq_P
---
Unroll the bounded verifier and emit its gate clauses with polynomially bounded loops.
-/
lemma circuit_machine (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
    ∃ circuits : Word → Lax429075.Circuits.Circuit,
      Nonempty (TM2ComputableInPolyTime id id
        (fun x => encodeCNF (Lax429075.Tseitin.encode (circuits x)))) ∧
      ∀ x, Lax429075.Circuits.Satisfiable (circuits x) ↔
        ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V := by
  obtain ⟨M, R, hM⟩ := VerifierCircuit.verifier_circuits V hV p
  exact ⟨fun x => VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length),
    verifier_polynomial_time M p R, fun x => (hM x).1⟩

end Lax429075Proofs.Streaming
