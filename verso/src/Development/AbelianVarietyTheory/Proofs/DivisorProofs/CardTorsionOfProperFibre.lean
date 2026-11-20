import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FibreTorsion

/- English proof (translation)
Introduce `S G _ _ hG g hg F _ _ p hprop N hN`. Set `B` to `(Over.pullback p).obj G`. Use `haveI : IsProper B.hom := hprop`. Establish `hB : IsAbelianScheme B` using `AbelianSchemeGerms.isAbelianScheme_of_proper B (IsSemiAbelian.pullback p G hG)`. Establish `hg' : SmoothOfRelativeDimension g B.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg`.

Establish `h` using `GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional F B g N hB hg' hN`. Establish `hp` using `isGrpPullback_pullback G p`. Establish `hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp F))))`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Establish `e : x.left ≫ pullback.fst G.hom p = y.left ≫ pullback.fst G.hom p` using `congrArg (fun z => z.left) hxy`. Conclude with `Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))`. Introduce `y`. Use `⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp F))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (hp.1.lift_fst _ _ _)`.

Set `e` to `MulEquiv.ofBijective _ hbij`. Establish `h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp F))).hom ≫ p) ⟶ G // x ^ N = 1} = N ^ (2 * g)`. Rewrite using `[← h]`. Use `(Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations. Use `show x ^ N = 1 ↔ e x ^ N = 1`.

Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`. Establish `h3 : (𝟙_ (Over (Sp F))).hom ≫ p = p` using `Category.id_comp p`. Rewrite `h2` using `[h3]`. Conclude with `h2`.
-/
theorem card_torsion_of_proper_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Sp F ⟶ S), IsProper (pullback.snd G.hom p) → ∀ N : ℕ, (N : F) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
  intro S G _ _ hG g hg F _ _ p hprop N hN
  let B := (Over.pullback p).obj G
  haveI : IsProper B.hom := hprop
  have hB : IsAbelianScheme B :=
    AbelianSchemeGerms.isAbelianScheme_of_proper B (IsSemiAbelian.pullback p G hG)
  have hg' : SmoothOfRelativeDimension g B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional F B g N hB hg' hN
  have hp := isGrpPullback_pullback G p
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp F)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom p = y.left ≫ pullback.fst G.hom p := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp F))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp F))).hom ≫ p) ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ N = 1 ↔ e x ^ N = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp F))).hom ≫ p = p := Category.id_comp p
  rw [h3] at h2
  exact h2

end GlobalTheory.FibreTorsion
