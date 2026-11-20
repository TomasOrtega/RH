import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealSheafDataMapSupComapClosedImmersion.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i → ∀ (a : T.IdealSheafData) (J : W.IdealSheafData), (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  first | exact @GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | exact GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | (intros; apply GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map <;> assumption)
