import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Introduce `S G _ hG N hN`. Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact.

Establish `hm : IsMonHom ((𝟙 G) ^ N)` using `GlobalTheory.AbLaw.MulN.isMonHom_mulA G N`. Establish `: LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `: LocallyOfFiniteType ((𝟙 G) ^ N).left` using `locallyOfFiniteType_of_comp _ G.hom`. Establish `: QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `: QuasiCompact ((𝟙 G) ^ N).left` using `QuasiCompact.of_comp _ G.hom`.

Use `GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance fun Ω _ _ t => ?_` and prove the remaining obligations. Simplify using `only [MonObj.comp_pow, Category.comp_id]`. Conclude with `GlobalTheory.HomExt.finite_torsion_points hG t hN`.
-/
theorem locallyQuasiFinite_pow_semiAbelian :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N →
      LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  intro S G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have : LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType ((𝟙 G) ^ N).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance
    fun Ω _ _ t => ?_
  simp only [MonObj.comp_pow, Category.comp_id]
  exact GlobalTheory.HomExt.finite_torsion_points hG t hN

end GlobalTheory.CompanionTheory.Ar.BT
