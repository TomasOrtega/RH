import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDiv

universe u

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun {W} a b h => W.affineOpenCover.openCover.hom_ext a b fun i => hinj (W.affineOpenCover.X i) (W.affineOpenCover.f i ≫ a) (W.affineOpenCover.f i ≫ b) ((Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm))⟩`.
-/
theorem mono_of_injective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : ∀ (R : CommRingCat.{u}) (a b : Spec R ⟶ X), a ≫ f = b ≫ f → a = b) : Mono f :=
  ⟨fun {W} a b h => W.affineOpenCover.openCover.hom_ext a b fun i =>
    hinj (W.affineOpenCover.X i) (W.affineOpenCover.f i ≫ a) (W.affineOpenCover.f i ≫ b)
      ((Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm))⟩

/- English proof (translation)
Establish `hm : Mono f` using `mono_of_injective_affinePts f fun R a b e => (h R).1 e`. Set `𝒰 : Y.OpenCover` to `Y.affineOpenCover.openCover`. Establish `hs : ∀ i : 𝒰.I₀, ∃ a : 𝒰.X i ⟶ X, a ≫ f = 𝒰.f i` using `fun i => (h (Y.affineOpenCover.X i)).2 (Y.affineOpenCover.f i)`. Use `choose g hg using hs`. Establish `hc : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j` using `fun i j => (cancel_mono f).1 (by`.

Simplify using `only [Category.assoc, hg]`. Conclude with `pullback.condition)`. Set `k : Y ⟶ X` to `𝒰.glueMorphisms g hc`. Establish `hk : k ≫ f = 𝟙 Y` using `𝒰.hom_ext _ _ fun i => by`. Establish `e` using `𝒰.ι_glueMorphisms g hc i`.

Simplify using `only [k, ← Category.assoc, e, hg, Category.comp_id]`. Use `⟨k, ?_, hk⟩` and prove the remaining obligations. Conclude with `(cancel_mono f).1 (by simp only [Category.assoc, hk, Category.comp_id, Category.id_comp])`.
-/
theorem isIso_of_bijective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}), Function.Bijective fun a : Spec R ⟶ X => a ≫ f) : IsIso f := by
  have hm : Mono f := mono_of_injective_affinePts f fun R a b e => (h R).1 e
  let 𝒰 : Y.OpenCover := Y.affineOpenCover.openCover
  have hs : ∀ i : 𝒰.I₀, ∃ a : 𝒰.X i ⟶ X, a ≫ f = 𝒰.f i := fun i =>
    (h (Y.affineOpenCover.X i)).2 (Y.affineOpenCover.f i)
  choose g hg using hs
  have hc : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => (cancel_mono f).1 (by
      simp only [Category.assoc, hg]
      exact pullback.condition)
  let k : Y ⟶ X := 𝒰.glueMorphisms g hc
  have hk : k ≫ f = 𝟙 Y := 𝒰.hom_ext _ _ fun i => by
    have e := 𝒰.ι_glueMorphisms g hc i
    simp only [k, ← Category.assoc, e, hg, Category.comp_id]
  refine ⟨k, ?_, hk⟩
  exact (cancel_mono f).1 (by simp only [Category.assoc, hk, Category.comp_id, Category.id_comp])

end PDiv

end GlobalTheory

namespace GlobalTheory

namespace PDiv

variable {O : Type} [CommRing O]

/- English proof (translation)
Set `ψ₀ : D →+* B` to `(Spec.preimage v.left).hom`. Establish `h0 : spMap ψ₀ = v.left` using `(congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage v.left)`. Establish `e : CommRingCat.ofHom (ψ₀.comp (algebraMap O D)) = CommRingCat.ofHom (algebraMap O B)` using `Spec.map_injective (by`. Express the relevant statement in the definitionally equal form `spMap (ψ₀.comp (algebraMap O D)) = spMap (algebraMap O B)`. Rewrite using `[Cris.spMap_comp, h0]`.

Conclude with `Over.w v)`. Establish `h1 : ψ₀.comp (algebraMap O D) = algebraMap O B` using `congrArg CommRingCat.Hom.hom e`. Conclude with `⟨{ ψ₀ with commutes' := RingHom.congr_fun h1 }, Over.OverMorphism.ext h0⟩`.
-/
theorem exists_spOver {B D : Type} [CommRing B] [Algebra O B] [CommRing D] [Algebra O D]
    (v : SpAlg O B ⟶ SpAlg O D) : ∃ ψ : D →ₐ[O] B, spOver ψ = v := by
  let ψ₀ : D →+* B := (Spec.preimage v.left).hom
  have h0 : spMap ψ₀ = v.left := (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans
    (Spec.map_preimage v.left)
  have e : CommRingCat.ofHom (ψ₀.comp (algebraMap O D)) = CommRingCat.ofHom (algebraMap O B) :=
    Spec.map_injective (by
      change spMap (ψ₀.comp (algebraMap O D)) = spMap (algebraMap O B)
      rw [Cris.spMap_comp, h0]
      exact Over.w v)
  have h1 : ψ₀.comp (algebraMap O D) = algebraMap O B := congrArg CommRingCat.Hom.hom e
  exact ⟨{ ψ₀ with commutes' := RingHom.congr_fun h1 }, Over.OverMorphism.ext h0⟩

/- English proof (translation)
The claim follows from `(congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage s)`.
-/
theorem spMap_preimage_toAlgebra {R : CommRingCat.{0}} (s : Spec R ⟶ Sp O) :
    @spMap O R _ _ (@algebraMap O R _ _ (Spec.preimage s).hom.toAlgebra) = s :=
  (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage s)

end PDiv

namespace PDivGroup.TorsionTower

open PDiv ReciprocityTheory.ChartRestriction.G.Semi

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  (t : G.TorsionTower A)

/- English proof (translation)
Rewrite using `[GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, t.y_pow]`. Both sides reduce to the same expression.
-/
theorem y_comp_mulN (n : ℕ) : t.y n ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] := by
  rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, t.y_pow]
  rfl

def toTorsion (n : ℕ) : SpAlg O (G.A n) ⟶ torsion A (p ^ n) :=
  pullback.lift (t.y n) (toUnit _) (t.y_comp_mulN n)

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
@[reassoc (attr := simp)] theorem toTorsion_ι (n : ℕ) : t.toTorsion n ≫ torsion.ι A (p ^ n) = t.y n :=
  pullback.lift_fst _ _ _

end PDivGroup.TorsionTower

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup.TorsionTower

open PDiv ReciprocityTheory.ChartRestriction.G.Semi

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  (t : G.TorsionTower A)

/- English proof (translation)
Introduce `a b e`. Express the relevant statement in the definitionally equal form `a ≫ (t.toTorsion n).left = b ≫ (t.toTorsion n).left at e`. Set `s` to `a ≫ (SpAlg O (G.A n)).hom`. Establish `hb : b ≫ (SpAlg O (G.A n)).hom = s`. Simplify using `only [s, ← Over.w (t.toTorsion n), ← Category.assoc, e]`.

Set `_ : Algebra O R` to `(Spec.preimage s).hom.toAlgebra`. Establish `hs : spMap (algebraMap O R) = s` using `spMap_preimage_toAlgebra s`. Set `a' : SpAlg O R ⟶ SpAlg O (G.A n)` to `Over.homMk a hs.symm`. Set `b' : SpAlg O R ⟶ SpAlg O (G.A n)` to `Over.homMk b (hb.trans hs.symm)`. Take `⟨φ, hφ⟩` from `exists_spOver a'`.

Take `⟨ψ, hψ⟩` from `exists_spOver b'`. Establish `hy : a' ≫ t.y n = b' ≫ t.y n`. Rewrite using `[← t.toTorsion_ι, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Conclude with `Over.OverMorphism.ext e`.

Rewrite `hy` using `[← hφ, ← hψ]`. Use `t.inj n R φ ψ hy` as an intermediate fact. Substitute `this` using the available equality. Conclude with `(congrArg Over.Hom.left hφ).symm.trans (congrArg Over.Hom.left hψ)`.
-/
theorem toTorsion_left_injective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Injective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro a b e
  change a ≫ (t.toTorsion n).left = b ≫ (t.toTorsion n).left at e
  let s := a ≫ (SpAlg O (G.A n)).hom
  have hb : b ≫ (SpAlg O (G.A n)).hom = s := by
    simp only [s, ← Over.w (t.toTorsion n), ← Category.assoc, e]
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let a' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk a hs.symm
  let b' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk b (hb.trans hs.symm)
  obtain ⟨φ, hφ⟩ := exists_spOver a'
  obtain ⟨ψ, hψ⟩ := exists_spOver b'
  have hy : a' ≫ t.y n = b' ≫ t.y n := by
    rw [← t.toTorsion_ι, ← Category.assoc, ← Category.assoc]
    congr 1
    exact Over.OverMorphism.ext e
  rw [← hφ, ← hψ] at hy
  have := t.inj n R φ ψ hy
  subst this
  exact (congrArg Over.Hom.left hφ).symm.trans (congrArg Over.Hom.left hψ)

/- English proof (translation)
Introduce `w`. Set `s` to `w ≫ (torsion A (p ^ n)).hom`. Set `_ : Algebra O R` to `(Spec.preimage s).hom.toAlgebra`. Establish `hs : spMap (algebraMap O R) = s` using `spMap_preimage_toAlgebra s`. Set `z : SpAlg O R ⟶ torsion A (p ^ n)` to `Over.homMk w hs.symm`.

Establish `hx : (z ≫ torsion.ι A (p ^ n)) ^ p ^ n = 1`. Establish `hc : torsion.ι A (p ^ n) ≫ mulN A (p ^ n) = toUnit _ ≫ η[A]` using `pullback.condition.trans (congrArg (· ≫ η[A]) (toUnit_unique _ _))`. Rewrite using `[← Category.comp_id (z ≫ torsion.ι A (p ^ n)), ← MonObj.comp_pow, ← GrpTangent.mulN_eq_pow, Category.assoc, hc, ← Category.assoc]`. Conclude with `(congrArg (· ≫ η[A]) (toUnit_unique _ _)).trans rfl`. Take `⟨φ, hφ⟩` from `t.surj n R _ hx`.

Establish `e : spOver φ ≫ t.toTorsion n = z`. Use `pullback.hom_ext ?_ (toUnit_unique _ _)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spOver φ ≫ t.toTorsion n ≫ torsion.ι A (p ^ n) = z ≫ torsion.ι A (p ^ n)`. Rewrite using `[toTorsion_ι, hφ]`. Conclude with `⟨(spOver φ).left, congrArg Over.Hom.left e⟩`.
-/
theorem toTorsion_left_surjective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Surjective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro w
  let s := w ≫ (torsion A (p ^ n)).hom
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let z : SpAlg O R ⟶ torsion A (p ^ n) := Over.homMk w hs.symm
  have hx : (z ≫ torsion.ι A (p ^ n)) ^ p ^ n = 1 := by
    have hc : torsion.ι A (p ^ n) ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] :=
      pullback.condition.trans (congrArg (· ≫ η[A]) (toUnit_unique _ _))
    rw [← Category.comp_id (z ≫ torsion.ι A (p ^ n)), ← MonObj.comp_pow,
      ← GrpTangent.mulN_eq_pow, Category.assoc, hc, ← Category.assoc]
    exact (congrArg (· ≫ η[A]) (toUnit_unique _ _)).trans rfl
  obtain ⟨φ, hφ⟩ := t.surj n R _ hx
  have e : spOver φ ≫ t.toTorsion n = z := by
    refine pullback.hom_ext ?_ (toUnit_unique _ _)
    change spOver φ ≫ t.toTorsion n ≫ torsion.ι A (p ^ n) = z ≫ torsion.ι A (p ^ n)
    rw [toTorsion_ι, hφ]
  exact ⟨(spOver φ).left, congrArg Over.Hom.left e⟩

instance isIso_toTorsion (n : ℕ) : IsIso (t.toTorsion n) := by
  have : IsIso ((Over.forget _).map (t.toTorsion n)) :=
    isIso_of_bijective_affinePts _ fun R =>
      ⟨t.toTorsion_left_injective n R, t.toTorsion_left_surjective n R⟩
  exact isIso_of_reflects_iso _ (Over.forget _)

def torsionIso (n : ℕ) : SpAlg O (G.A n) ≅ torsion A (p ^ n) :=
  haveI := t.isIso_toTorsion n
  asIso (t.toTorsion n)

/- English proof (translation)
The claim follows from `t.toTorsion_ι n`.
-/
@[reassoc (attr := simp)] theorem torsionIso_hom_ι (n : ℕ) :
    (t.torsionIso n).hom ≫ torsion.ι A (p ^ n) = t.y n :=
  t.toTorsion_ι n

/- English proof (translation)
Rewrite using `[Iso.inv_comp_eq, torsionIso_hom_ι]`.
-/
@[reassoc (attr := simp)] theorem torsionIso_inv_y (n : ℕ) :
    (t.torsionIso n).inv ≫ t.y n = torsion.ι A (p ^ n) := by
  rw [Iso.inv_comp_eq, torsionIso_hom_ι]

/- English proof (translation)
Introduce `p O _ G A _ t n`. Conclude with `IsPullback.of_iso_pullback ⟨t.y_comp_mulN n⟩ (t.torsionIso n) (t.torsionIso_hom_ι n) (pullback.lift_snd _ _ _)`.
-/
theorem isPullback_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : G.TorsionTower A) (n : ℕ), IsPullback (t.y n) (toUnit _) (mulN A (p ^ n)) η[A] := by
  intro p O _ G A _ t n
  exact IsPullback.of_iso_pullback ⟨t.y_comp_mulN n⟩ (t.torsionIso n) (t.torsionIso_hom_ι n)
    (pullback.lift_snd _ _ _)

end PDivGroup.TorsionTower

end GlobalTheory
