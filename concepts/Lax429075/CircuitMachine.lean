import Lax429075.Tseitin
import Lax429075.Encoding
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: Polynomial circuit simulation of a verifier
type: lemma
---
For a fixed polynomial time verifier and polynomial certificate bound,
construct a circuit whose free inputs represent the certificate. The circuit
is satisfiable exactly when some bounded certificate is accepted. Its encoded
gate clauses are produced in polynomial time. The machine simulation and
time bound are open proof obligations.
-/

namespace Lax429075.CircuitMachine

open Lax434930.PolynomialTime Lax434930.Certificates Circuits Encoding

axiom compile (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
  ∃ circuits : Word → Circuit,
    Nonempty (Turing.TM2ComputableInPolyTime id id
      (fun x => encodeCNF (Tseitin.encode (circuits x)))) ∧
    ∀ x, Satisfiable (circuits x) ↔
      ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V

end Lax429075.CircuitMachine
