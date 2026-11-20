import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsRescaleByGeneratorMultiple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaSeriesTermsRescaleByGeneratorMultiple.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D F N) (th : H0 D.P.L 1) (r : R), (∀ j, ν.th.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D.P.L 1, ∃ r' : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r') * th.f j) → ∃ (N' : GlobalTheory.Ex.NumD F) (ν' : GlobalTheory.Ex.NumOf D F N') (e : N'.X ≃+ N.X), ν'.th = th ∧ ∀ (m : ℕ) (p : QkPt D F (m ^ 2)) (q : N.QT (m ^ 2)) (q' : N'.QT (m ^ 2)), ν.QPt p q → ν'.QPt p q' → ∀ χ, N.txT m q (e χ) = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.txT m q' χ := by
  first | exact @GlobalTheory.Mum.Rescale.txT_rescale | exact GlobalTheory.Mum.Rescale.txT_rescale | (intros; apply GlobalTheory.Mum.Rescale.txT_rescale <;> assumption)
