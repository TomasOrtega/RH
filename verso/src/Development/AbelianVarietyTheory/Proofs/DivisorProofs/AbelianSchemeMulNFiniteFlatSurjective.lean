import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.MulFlatSurj

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, ← ih]`. Both sides reduce to the same expression.
-/
theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

/- English proof (translation)
Introduce `R _ A _ hA n hn`. Establish `hc` using `hA.comm`. Take `⟨h1, h2⟩` from `GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp R) A hA n hn`. Establish `e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n` using `mulN_eq_pow A n`. Rewrite using `[e]`.

Use `⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩` and prove the remaining obligations. Establish `hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left` using `MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1`. Rewrite `hf`, the goal using `[GlobalTheory.MulFiniteFlat.pullback_map_mulA]`. Establish `hB` using `ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA`. Establish `hBc` using `hB.comm`.

Conclude with `(GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _ hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2`.
-/
theorem finite_flat_surjective_mulN : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro R _ A _ hA n hn
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp R) A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

end GlobalTheory.MulFlatSurj
