import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsAway

/- English proof (translation)
Introduce `R _ _ f _ G _ G' _ π hπ n`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Establish `: Subsingleton (Localization.Away (0 : R))` using `IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩`. Conclude with `not_subsingleton (Localization.Away (0 : R)) this`.

Establish `hle : Submonoid.powers f ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`. Establish `hinj : Function.Injective (algebraMap R (Localization.Away f))` using `IsLocalization.injective _ hle`. Prove the components needed by the constructor for the conclusion. Conclude with `GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ`. Introduce `h K _ _ κ x hx`.

Use `letI : Algebra (Localization.Away f) (FractionRing R) := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle`. Use `haveI : IsScalarTower R (Localization.Away f) (FractionRing R) := IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle`. Use `haveI : IsFractionRing (Localization.Away f) (FractionRing R) := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f) (FractionRing R)`. Set `e` to `FractionRing.algEquiv (Localization.Away f) (FractionRing R)`. Set `j : FractionRing (Localization.Away f) →+* FractionRing R` to `e.toAlgHom.toRingHom`.

Establish `hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) = algebraMap R (FractionRing R) r`. Introduce `r`. Conclude with `(e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm`. Establish `hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R` using `by show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) = spMap (algebraMap R (FractionRing R))`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]`.

Conclude with `congrArg spMap (RingHom.ext hj)`. Set `T : Over (Sp (Localization.Away f))` to `Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))`. Establish `hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R` using `by show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]`. Set `e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R)` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)`.

Set `x'` to `(GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)`. Establish `hx' : x' ^ n = 1`. Simplify using `only [x']`. Rewrite using `[← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]`. Take `⟨y, hy⟩` from `h K (κ.comp j) x' hx'`.

Establish `hyw : y.left ≫ G'.hom = jK (Localization.Away f)` using `Over.w y`. Use `⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩` and prove the remaining obligations. Use `show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R`. Rewrite using `[Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]`. Conclude with `hsq`.

Use `show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π`. Establish `h1 : x'.left ≫ π = x.left` using `(GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)`. Rewrite using `[← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]`. Simplify using `only [Category.assoc]`.
-/
theorem torsRat_away_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R) [IsDomain (Localization.Away f)] (G : Over (Sp R))
    [GrpObj G] (G' : Over (Sp (Localization.Away f))) [GrpObj G'] (π : G'.left ⟶ G.left),
    IsGrpPullback G' G (spMap (algebraMap R (Localization.Away f))) π → ∀ n : ℕ,
      GlobalTheory.TChart.TorsRat G n ↔ GlobalTheory.TChart.TorsRat G' n := by
  intro R _ _ f _ G _ G' _ π hπ n
  have hf : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩
    exact not_subsingleton (Localization.Away (0 : R)) this
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  constructor
  · exact GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ
  · intro h K _ _ κ x hx
    letI : Algebra (Localization.Away f) (FractionRing R) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsFractionRing (Localization.Away f) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f)
        (FractionRing R)
    let e := FractionRing.algEquiv (Localization.Away f) (FractionRing R)
    let j : FractionRing (Localization.Away f) →+* FractionRing R := e.toAlgHom.toRingHom
    have hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) =
        algebraMap R (FractionRing R) r := by
      intro r
      exact (e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
    have hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R := by
      show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) =
        spMap (algebraMap R (FractionRing R))
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      exact congrArg spMap (RingHom.ext hj)
    let T : Over (Sp (Localization.Away f)) := Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))
    have hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R := by
      show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]
    let e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
    let x' := (GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)
    have hx' : x' ^ n = 1 := by
      simp only [x']
      rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    obtain ⟨y, hy⟩ := h K (κ.comp j) x' hx'
    have hyw : y.left ≫ G'.hom = jK (Localization.Away f) := Over.w y
    refine ⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩
    · show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R
      rw [Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]
      exact hsq
    · show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π
      have h1 : x'.left ≫ π = x.left :=
        (GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)
      rw [← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      simp only [Category.assoc]

end GlobalTheory.TorsAway
