import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFibreRegularLocalRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothFibreRegularLocalRing.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.smooth_fibre_regular_local_ring : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) [Smooth π] (y : Y), IsRegularLocalRing (Y.presheaf.stalk y ⧸ (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  first | exact @GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal | exact GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal | (intros; apply GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal <;> assumption)
