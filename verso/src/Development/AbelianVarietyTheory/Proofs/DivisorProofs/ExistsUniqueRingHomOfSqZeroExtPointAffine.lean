import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

/- English proof (translation)
Use `Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal`.

Establish `hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal` using `y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)`. Establish `hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd` using `(TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hx]`.

Conclude with `y.asIdeal.add_mem h hm`. Introduce `h`. Establish `e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd`. Rewrite using `[eq_sub_iff_add_eq]`. Conclude with `TrivSqZeroExt.inl_fst_add_inr_snd_eq x`.

Rewrite using `[e]`. Conclude with `y.asIdeal.sub_mem h hm`.
-/
theorem range_spMap_fst_eq (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y
  apply PrimeSpectrum.ext
  ext x
  change (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal
  have hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal :=
    y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  constructor
  · intro h; rw [hx]; exact y.asIdeal.add_mem h hm
  · intro h
    have e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd := by
      rw [eq_sub_iff_add_eq]; exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    rw [e]; exact y.asIdeal.sub_mem h hm

/- English proof (translation)
Establish `hr : Set.range z ⊆ Set.range (affPt s U)`. Introduce and unpack `_ ⟨y, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by`. Rewrite using `[range_spMap_fst_eq]`. Discharge the goal by the elementary cases of `trivial`.

Use `⟨spMap ρ x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x`. Rewrite using `[hz]`. Use `haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2`. Use `set g := IsOpenImmersion.lift (affPt s U) z hr with hg`.

Establish `hgf : g ≫ affPt s U = z` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c'` using `fun c c' h ↦ by`. Establish `h'` using `(cancel_mono (affPt s U)).1 h`. Use `Spec.map_injective h'` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.

Establish `hsp' : ∀ c c' : Sec s U.1 →+* B, spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c'` using `fun c c' h ↦ by`. Establish `h'` using `(cancel_mono (affPt s U)).1 h`. Use `Spec.map_injective h'` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`. Use `set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀`.

Establish `hc : spMap c₀ = g` using `Spec.map_preimage g`. Establish `h₁ : spMap c₀ ≫ affPt s U = z` using `by rw [hc, hgf]`. Use `⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩` and prove the remaining obligations. Establish `e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U = spMap ρ ≫ affPt s U`. Rewrite using `[← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]`.

Both sides reduce to the same expression. Introduce `b`. Conclude with `congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)`.
-/
theorem exists_unique_ringHom_of_sqZero (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X)
    (hz : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U) :
    ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  have hr : Set.range z ⊆ Set.range (affPt s U) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
      rw [range_spMap_fst_eq]; trivial
    refine ⟨spMap ρ x, ?_⟩
    change (spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x
    rw [hz]
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  set g := IsOpenImmersion.lift (affPt s U) z hr with hg
  have hgf : g ≫ affPt s U = z := IsOpenImmersion.lift_fac _ _ _
  have hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  have hsp' : ∀ c c' : Sec s U.1 →+* B,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀
  have hc : spMap c₀ = g := Spec.map_preimage g
  have h₁ : spMap c₀ ≫ affPt s U = z := by rw [hc, hgf]
  refine ⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩
  have e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U =
      spMap ρ ≫ affPt s U := by
    rw [← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  intro b
  exact congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)

end GlobalTheory.AbTan
