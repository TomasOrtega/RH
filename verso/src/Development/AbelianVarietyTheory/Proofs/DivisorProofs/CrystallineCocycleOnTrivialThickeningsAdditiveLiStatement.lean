import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLi
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PtExt.fv_linear` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCrystallineCocycleOnTrivialThickeningsAdditiveLi.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧ (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D), fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧ (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)), ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  first | exact @GlobalTheory.PtExt.fv_linear | exact GlobalTheory.PtExt.fv_linear | (intros; apply GlobalTheory.PtExt.fv_linear <;> assumption)
