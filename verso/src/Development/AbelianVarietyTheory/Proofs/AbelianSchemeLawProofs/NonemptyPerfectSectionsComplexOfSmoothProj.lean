import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineChartsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModelStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

/- English proof (translation)
Introduce `R _ X f hf hp M hM`. Take `⟨H, hH, m, s, hs⟩` from `hp`. Take `⟨K, φ, hK⟩` from `GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle R X f H m s M hH hM hs hf`. Conclude with `GlobalTheory.T.threeTermComplex_of_projective_cech_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1 (GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts R X f H m s hH hs).2.2 hK`.
-/
theorem nonempty_perf_of_smooth_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  intro R _ X f hf hp M hM
  obtain ⟨H, hH, m, s, hs⟩ := hp
  obtain ⟨K, φ, hK⟩ := GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle R X f H m s M hH hM hs hf
  exact GlobalTheory.T.threeTermComplex_of_projective_cech_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1
    (GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts R X f H m s hH hs).2.2 hK

end GlobalTheory.AbLaw
