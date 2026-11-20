import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionTwistedLineBundleNonzeroClosedFibre.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left), D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | exact GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | (intros; apply GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre <;> assumption)
