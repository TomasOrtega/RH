import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsAlgHomFunctionFieldOfSpecializesGenericPoi.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X), q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) → ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  first | exact @GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | exact GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | (intros; apply GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint <;> assumption)
