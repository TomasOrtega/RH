import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCohomologySubsingletonOfCechPicardClassEq.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB), cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) → Subsingleton (coh (LB.toMod N) q) := by
  first | exact @GlobalTheory.Div.coh_subsingleton_of_cls_eq | exact GlobalTheory.Div.coh_subsingleton_of_cls_eq | (intros; apply GlobalTheory.Div.coh_subsingleton_of_cls_eq <;> assumption)
