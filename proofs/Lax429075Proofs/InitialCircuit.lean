import Lax429075Proofs.InitialCircuitCells
import Lax429075Proofs.MachineUniformBlocks

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax434930.Certificates Lax429075.CNF
open Lax554803.MachineModels CircuitBuilder WindowMachine
open scoped Classical

noncomputable def initialBit (M : SingleTape) (x : Word) (bound radius : ℕ)
    (b : MachineCircuit.Bit M radius) : Expr :=
  match b with
  | .inl q => pad 5 (.constant (decide ((default : M.Q) = q)))
  | .inr (.inl i) => pad 5 (.constant (decide (position radius 0 = i)))
  | .inr (.inr (i, a)) => initialCell M x bound (coordinate radius i) a

lemma initialBit_bounded (M : SingleTape) (x : Word) (bound radius : ℕ)
    (b : MachineCircuit.Bit M radius) : (initialBit M x bound radius b).Bounded (inputCount bound) := by
  rcases b with q | i | ⟨i, a⟩
  · exact pad_bounded _ _ _ trivial
  · exact pad_bounded _ _ _ trivial
  · exact initialCell_bounded _ _ _ _ _

lemma initialBit_cost (M : SingleTape) (x : Word) (bound radius : ℕ)
    (b : MachineCircuit.Bit M radius) : (initialBit M x bound radius b).cost = 11 := by
  rcases b with q | i | ⟨i, a⟩ <;> simp [initialBit, initialCell_cost, pad_cost, Expr.cost]

lemma initialBit_word (M : SingleTape) (x : Word) (bound radius : ℕ)
    (b : MachineCircuit.Bit M radius) (ρ : Assignment) (y : Word) (hy : y.length ≤ bound)
    (hlive : ∀ i, live bound ρ i = true ↔ i < y.length)
    (hdata : ∀ i, i < y.length → y[i]? = some (ρ (dataPort i))) :
    (initialBit M x bound radius b).eval ρ =
      MachineCircuit.bitValue M radius (initial M radius (pair x y)) b := by
  rcases b with q | i | ⟨i, a⟩
  · simp [initialBit, pad_eval, Expr.eval, MachineCircuit.bitValue, initial, AbsoluteTape.initial]
  · simp [initialBit, pad_eval, Expr.eval, MachineCircuit.bitValue, initial]
  · exact initialCell_word M x bound _ a ρ y hy hlive hdata

noncomputable def initialExpressions (M : SingleTape) (x : Word) (bound radius : ℕ) :
    Fin (MachineCircuit.bitCount M radius) → Expr :=
  fun i => initialBit M x bound radius ((MachineCircuit.bitEquiv M radius).symm i)

lemma initialExpressions_word (M : SingleTape) (x : Word) (bound radius : ℕ)
    (ρ : Assignment) (y : Word) (hy : y.length ≤ bound)
    (hlive : ∀ i, live bound ρ i = true ↔ i < y.length)
    (hdata : ∀ i, i < y.length → y[i]? = some (ρ (dataPort i))) :
    (fun i => (initialExpressions M x bound radius i).eval ρ) =
      MachineCircuit.encode M radius (initial M radius (pair x y)) := by
  funext i
  exact initialBit_word M x bound radius _ ρ y hy hlive hdata

lemma initialVector_size (M : SingleTape) (x : Word) (bound radius start : ℕ) :
    (compileVector start (initialExpressions M x bound radius)).gates.length =
      MachineCircuit.bitCount M radius * 11 := by
  simp [compileVector, compileMany_length, List.map_ofFn, Function.comp_def,
    initialExpressions, initialBit_cost]

end Lax429075Proofs.CertificateCircuit
