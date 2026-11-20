import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.LCSecFub

open Ad3.K.LC Ad3.K.LC.B in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem secFub_of_secJ : Ad3.K.LC.B.SecJ → Ad3.K.LC.B.SecFub := by
  intro hJ k hk Ψ g
  have hI : Integrable (secI k Ψ g) ((volume : Measure M22).prod (volume : Measure ℂ)) := hJ k hk Ψ g
  have hprod : ∫ p : M22 × ℂ, secI k Ψ g p = ∫ h : M22, ∫ t : ℂ, secI k Ψ g (h, t) :=
    integral_prod _ hI
  rw [hprod]
  unfold sec
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [secI]
  rw [integral_mul_const, integral_mul_const]

end GlobalTheory.CompanionTheory.LCSecFub
