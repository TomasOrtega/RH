import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPoint
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionTwistNonvanishingRationalPoint.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | exact GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus <;> assumption)
