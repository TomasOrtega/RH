import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlargeLoc

/- English proof (translation)
Introduce `T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker`. Use `set L := Localization.AtPrime QA₁`. Use `set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}`. Establish `hI : I ≤ maximalIdeal O`. Rewrite using `[Ideal.span_le]`.

Simplify using `using hX`. Establish `hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y)`. Introduce `y`. Assume the negation of the conclusion as `hy`. Establish `h1 : ρ' y ∈ maximalIdeal A₁` using `(mem_maximalIdeal _).2 hy`.

Establish `h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))`. Establish `h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O`.

Use `hI (hcong y)` as an intermediate fact. Use `(maximalIdeal O).sub_mem h2 this` as an intermediate fact. Simplify using `using this`. Establish `h4 : IsUnit (jA₁ (algebraMap EA₁ L y))` using `(IsLocalization.map_units L y).map jA₁`. Conclude with `(mem_maximalIdeal _ |>.1 h3) h4`.

Set `ρ₁ : L →+* A₁` to `IsLocalization.lift (M := QA₁.primeCompl) hunit`. Establish `hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ'`. Use extensionality with `x`. Conclude with `IsLocalization.lift_eq _ _`. Use `⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[RingHom.mem_ker]`. Take `⟨⟨x, y⟩, rfl⟩` from `IsLocalization.mk'_surjective QA₁.primeCompl z`.

Simplify using `only at hz ⊢`. Establish `hx : ρ' x = 0`. Use `IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y` as an intermediate fact. Express the relevant statement in the definitionally equal form `ρ₁ _ = _ at this`. Rewrite `this` using `[hz]`.

Conclude with `(Units.mul_left_eq_zero _).1 this.symm`. Take `⟨s, hs, hsx⟩` from `hker x hx`. Establish `hsy : s * (y : EA₁) ∈ QA₁.primeCompl` using `QA₁.primeCompl.mul_mem hs y.2`. Establish `heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl)`. Rewrite using `[IsLocalization.mk'_eq_iff_eq]`.

Simplify using `only`. Put the polynomial expressions in normal form. Rewrite using `[heq, IsLocalization.mk'_eq_mul_mk'_one]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Establish `: algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L)` using `Ideal.mem_map_of_mem _ hsx`.

Rewrite `this` using `[Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]`. Then use the resulting hypothesis. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]`. Express the relevant statement in the definitionally equal form `(ρ₁.comp (algebraMap EA₁ L)) _ = 0`. Rewrite using `[hcomp, hρX]`. Establish `key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁`.

Apply `IsLocalization.ringHom_ext QA₁.primeCompl` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq]`. Use `hcong x` as an intermediate fact.

Rewrite `this` using `[← hcomp]`. Simplify using `using this`. Introduce `x`. Use `congrArg (fun f => f x) key` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`.

Conclude with `Ideal.Quotient.eq.1 this`.
-/
theorem retract_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  intro T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker
  set L := Localization.AtPrime QA₁
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hI : I ≤ maximalIdeal O := by
    rw [Ideal.span_le]; simpa using hX
  have hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y) := by
    intro y
    by_contra hy
    have h1 : ρ' y ∈ maximalIdeal A₁ := (mem_maximalIdeal _).2 hy
    have h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))
    have h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O := by
      have := hI (hcong y)
      have := (maximalIdeal O).sub_mem h2 this
      simpa using this
    have h4 : IsUnit (jA₁ (algebraMap EA₁ L y)) :=
      (IsLocalization.map_units L y).map jA₁
    exact (mem_maximalIdeal _ |>.1 h3) h4
  let ρ₁ : L →+* A₁ := IsLocalization.lift (M := QA₁.primeCompl) hunit
  have hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ' := by
    ext x; exact IsLocalization.lift_eq _ _
  refine ⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩
  · rw [IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]
  · apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective QA₁.primeCompl z
      dsimp only at hz ⊢
      have hx : ρ' x = 0 := by
        have := IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y
        change ρ₁ _ = _ at this
        rw [hz] at this
        exact (Units.mul_left_eq_zero _).1 this.symm
      obtain ⟨s, hs, hsx⟩ := hker x hx
      have hsy : s * (y : EA₁) ∈ QA₁.primeCompl := QA₁.primeCompl.mul_mem hs y.2
      have heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only
        ring_nf
      rw [heq, IsLocalization.mk'_eq_mul_mk'_one]
      apply Ideal.mul_mem_right
      have : algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L) :=
        Ideal.mem_map_of_mem _ hsx
      rwa [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply] at this
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]
      change (ρ₁.comp (algebraMap EA₁ L)) _ = 0
      rw [hcomp, hρX]
  · have key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁ := by
      apply IsLocalization.ringHom_ext QA₁.primeCompl
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq]
      have := hcong x
      rw [← hcomp] at this
      simpa using this
    intro x
    have := congrArg (fun f => f x) key
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

end GlobalTheory.KeyOriginEnlargeLoc
