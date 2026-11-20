import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AlgebraicApproximationValued
open Formalism.L2.Pj

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FCommonZeroEvaluation%2FAlgebraicApproximationValued.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @ModelDimension.algebraic_approximation_valued | exact ModelDimension.algebraic_approximation_valued
