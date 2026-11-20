import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ)` using `(IsFractionRing.injective W (FractionRing W)).comp hφ`. Use `⟨IsFractionRing.lift hinj, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Simplify using `only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]`. Use extensionality with `x`.

Take `⟨r, r', hr', h⟩` from `IsFractionRing.div_surjective (A := R) (a x)`. Establish `h0 : algebraMap R (FractionRing R) r' ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'`. Establish `hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y` using `fun y => RingHom.congr_fun hac y`. Establish `hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y` using `fun y => RingHom.congr_fun hbc y`. Establish `h1 : x * c r' = c r`.

Apply `ha` to reduce the goal to its premises. Rewrite using `[map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]`. Establish `h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0`. Introduce `h3`. Conclude with `nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))`.

Rewrite using `[RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]`.
-/
theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

/- English proof (translation)
Introduce `R _ _ M W _ _ φ hφ ξ hξ`. Use `haveI := M.integral`. Use `haveI := M.dominant`. Set `s : M.S` to `(jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))`. Take `⟨B, f, hf, hs, -⟩` from `M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial`.

Establish `hb : Set.range (jK W ≫ ξ) ⊆ Set.range f`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `: y = IsLocalRing.closedPoint (FractionRing W)` using `Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _`. Rewrite using `[this]`. Conclude with `hs`.

Establish `ha : Set.range M.gp ⊆ Set.range f`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨z, hz⟩` from `M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩`. Establish `: y = z` using `Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _`. Rewrite using `[this]`.

Conclude with `hz`. Take `⟨a, ha'⟩` from `Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)`. Take `⟨b, hb'⟩` from `Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)`. Take `⟨c, hc'⟩` from `Spec.map_surjective (f ≫ M.π)`. Establish `e1 : Spec.map a ≫ f = M.gp` using `by rw [ha', IsOpenImmersion.lift_fac]`.

Establish `e2 : Spec.map b ≫ f = jK W ≫ ξ` using `by rw [hb', IsOpenImmersion.lift_fac]`. Establish `hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]`. Establish `hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W))`.

Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]`. Establish `hred : IsReduced (Spec B)` using `isReduced_of_isOpenImmersion f`. Establish `hred' : _root_.IsReduced B` using `(affine_isReduced_iff B).1 hred`. Establish `hdom : IsDominant (Spec.map a)` using `by haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant`.

Conclude with `IsDominant.of_comp_of_isOpenImmersion _ f`. Establish `hainj : Function.Injective a.hom`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1` as an intermediate fact. Rewrite `this` using `[nilradical_eq_zero]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)`.

Take `⟨ψ, h1, h2⟩` from `exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)`. Use `⟨ψ, h1, ?_⟩` and prove the remaining obligations. Establish `h3 : a ≫ CommRingCat.ofHom ψ = b` using `by ext1; exact h2`. Rewrite using `[← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]`.
-/
theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
