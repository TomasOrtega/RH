import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionTranslateTensorFibreNonvanishing.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left), ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | exact GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus <;> assumption)
