import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.SiegUniqBase

section FlatPow
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

/- English proof (translation)
Introduce `S A _ hA k hk`. Establish `hc` using `hA.comm`. Take `⟨h1, h2⟩` from `GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA k hk`. Establish `e : (𝟙 A) ^ k = ReciprocityTheory.ChartRestriction.G.Out.mulA A k` using `rfl`. Rewrite using `[e]`.

Use `⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩` and prove the remaining obligations. Establish `hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A k)).left` using `MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1`. Rewrite `hf`, the goal using `[GlobalTheory.MulFiniteFlat.pullback_map_mulA]`. Establish `hB` using `ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA`. Establish `hBc` using `hB.comm`.

Conclude with `(GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _ hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ k) hf).2`.
-/
theorem flat_surjective_qc_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ k : ℕ, 0 < k → Flat ((𝟙 A) ^ k).left ∧ Surjective ((𝟙 A) ^ k).left ∧ QuasiCompact ((𝟙 A) ^ k).left := by
  intro S A _ hA k hk
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA k hk
  have e : (𝟙 A) ^ k = ReciprocityTheory.ChartRestriction.G.Out.mulA A k := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A k)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ k) hf).2

end FlatPow

end GlobalTheory.UPel.HT.SiegUniqBase
