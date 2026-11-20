import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Introduce `n χ`. Establish `hr : Formalism.QuantumDeterminants.rhoStd n = rhoV n` using `rfl`. Rewrite using `[GlobalTheory.CasimirEigen.gelfVal_two_eq, hr, nsq]`. Use `push_cast`. Simplify using `only [sq]`.
-/
theorem UpperTheory.RealTr.gelf2 :
    ∀ (n : ℕ) (χ : Fin n → ℂ), GlobalTheory.Dec.gelfVal χ 2 = ∑ a, χ a ^ 2 - (nsq (rhoV n) : ℂ) := by
  intro n χ
  have hr : Formalism.QuantumDeterminants.rhoStd n = rhoV n := rfl
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, hr, nsq]
  push_cast
  simp only [sq]
