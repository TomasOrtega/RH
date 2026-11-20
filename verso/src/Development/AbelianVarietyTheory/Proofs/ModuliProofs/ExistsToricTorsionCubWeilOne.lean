import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

/- English proof (translation)
Introduce `h3 X G _ _ hG L c g N k _ _ x dG hN`. Set `G' : Over (Sp k)` to `(Over.pullback x).obj G`. Establish `hp : IsGrpPullback G' G x (pullback.fst G.hom x)` using `isGrpPullback_pullback G x`. Establish `hG' : IsSemiAbelian G'` using `IsSemiAbelian.pullback x G hG`. Use `hG'.comm` as an intermediate fact.

Use `hG'.smooth` as an intermediate fact. Use `hG'.geomConnected` as an intermediate fact. Establish `dG' : SmoothOfRelativeDimension g G'.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 dG`. Take `⟨E⟩` from `hG.fibres k x`. Set `` to `E.addCommGroup`.

Set `` to `E.grpB`. Use `E.free` as an intermediate fact. Use `E.finite` as an intermediate fact. Use `E.i_hom` as an intermediate fact. Take `⟨hL, hr, ⟨c', hc'⟩, -⟩` from `h3.cubePull _ _ G G' (cubeMapOf hp) L c`.

Take `⟨σ⟩` from `GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom`. Establish `hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x` using `pullback.condition`. Set `U : Over (Sp k)` to `𝟙_ (Over (Sp k))`. Set `ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x)` to `Over.homMk (𝟙 _) rfl`. Set `φ : (U ⟶ G') →* (Over.mk x ⟶ G)` to `(preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)`.

Establish `hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x` using `fun a => Category.id_comp _`. Establish `hb : Function.Bijective φ`. Use `⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, ← hφ, h]`. Conclude with `(Over.w a).trans (Over.w b).symm`.

Use `⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩` and prove the remaining obligations. Set `e` to `MulEquiv.ofBijective φ hb`. Establish `he : ∀ a : U ⟶ G', e a ^ N = 1 ↔ a ^ N = 1` using `fun a => by rw [← map_pow, e.map_eq_one_iff]`. Establish `hcount` using `GlobalTheory.card_torsion_mul_card_toric_torsion k G' E g N hG' dG' hN`. Use `⟨e '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ⟨ha, -⟩, rfl⟩`. Conclude with `(he a).2 ha`. Introduce and unpack `_ ⟨_, ⟨ha, t, rfl⟩, rfl⟩ y hy`. Take `⟨b, rfl⟩` from `e.surjective y`. Establish `ht : t ^ N = 1` using `E.isKernel.hom_ext (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)`.

Establish `h1` using `σ.cubWeil ht ((he b).1 hy)`. Establish `h2` using `(GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) L _ c c' hc' N U _ _ _ h1).comp ρ`. Rewrite `h2` using `[map_one]`. Conclude with `h2`. Rewrite using `[← hcount]`.

Use `congr 1`. Conclude with `(Nat.card_congr (e.toEquiv.subtypeEquiv fun a => (he a).symm)).symm`. Conclude with `Nat.card_image_of_injective e.injective _`.
-/
theorem exists_toric_torsion_cubWeil_one : Out.Laws3 → ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : RigLB G) (c : CubicalStr G L) (g N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → ∃ T : Set (Over.mk x ⟶ G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ y : Over.mk x ⟶ G, y ^ N = 1 → CubWeil c N τ y 1) ∧ Nat.card {p : Over.mk x ⟶ G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro h3 X G _ _ hG L c g N k _ _ x dG hN
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension g G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 dG
  obtain ⟨E⟩ := hG.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) L c
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E g N hG' dG' hN
  refine ⟨e '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, t, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e.surjective y
    have ht : t ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) L _ c c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e.injective _

end GlobalTheory
