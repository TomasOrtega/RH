import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSchwartzUnitaryIntertwinerScalar.lean&line=125#L125)
-/
theorem _root_.GlobalTheory.T.schwartz_unitary_intertwiner_scalar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  first | exact @GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz | exact GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz | (intros; apply GlobalTheory.RealWeil.SchurSchwartz.schur_schwartz <;> assumption)
