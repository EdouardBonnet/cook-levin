import Lax429075Proofs.VerifierCircuit

namespace Lax429075Proofs.VerifierCircuit

open Lax434930.PolynomialTime Lax429075.CNF Lax429075.Circuits
open Lax434930.MachineModels CircuitBuilder CertificateCircuit MachineCircuit

lemma prefixExpr_cost (bound : ℕ) : (prefixExpr bound).cost = 3 * (bound - 1) + 1 := by
  simp [prefixExpr, allExpr_cost, List.map_map, Function.comp_def, Expr.cost, Nat.mul_comm] <;> omega

lemma preparation_size (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (preparation M x bound radius).gates.length = bitCount M radius * 11 :=
  initialVector_size M x bound radius (inputCount bound)

lemma simulation_size (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (simulation M x bound radius).gates.length = radius * bitCount M radius * blockSize M radius :=
  machine_rounds_size_exact M radius _ radius _

lemma conclusion_size (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (conclusion M x bound radius).gates.length = 3 * (bound - 1) + 3 * Fintype.card M.Q + 3 := by
  simp [conclusion, compile_length, conclusionExpr, Expr.cost, cost_rename,
    prefixExpr_cost, acceptanceExpr_cost] <;> omega

lemma circuit_size (M : SingleTape) (x : Word) (bound radius : ℕ) :
    (circuit M x bound radius).gates.length =
      inputCount bound + bitCount M radius * 11 + radius * bitCount M radius * blockSize M radius +
        3 * (bound - 1) + 3 * Fintype.card M.Q + 3 := by
  simp [circuit, assemble, body, preparation_size, simulation_size, conclusion_size] <;> omega

noncomputable def sizePolynomial (M : SingleTape) (p R : Polynomial ℕ) : Polynomial ℕ :=
  let W := 2 * R + 1
  let N := Polynomial.C (Fintype.card M.Q) + W + W * Polynomial.C (Fintype.card M.Γ)
  let K := 5 * Polynomial.C (Fintype.card M.Q) * W * Polynomial.C (Fintype.card M.Γ) + 1
  (2 * p + 1) + N * 11 + R * N * K + 3 * p + 3 * Polynomial.C (Fintype.card M.Q) + 3

lemma circuit_polynomial_size (M : SingleTape) (p R : Polynomial ℕ) (x : Word) :
    (circuit M x (p.eval x.length) (R.eval x.length)).gates.length ≤
      (sizePolynomial M p R).eval x.length := by
  rw [circuit_size]
  simp only [sizePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_C, inputCount, bitCount, blockSize, Nat.add_assoc]
  omega

end Lax429075Proofs.VerifierCircuit
