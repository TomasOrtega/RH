import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `L _ c R hR`. Use `letI := hR.isLocalRing`. Use `letI : Algebra ℂ R := (c.codRestrict R hR.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType`. Take `⟨σ, hσ⟩` from `(Algebra.essFiniteType_iff ℂ R).mp inferInstance`.

Use `set A := Algebra.adjoin ℂ (σ : Set R) with hA`. Set `S : Subring L` to `A.toSubring.map R.subtype`. Establish `hSR : S ≤ R`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.2`.

Establish `memS : ∀ x : R, x ∈ A → (x : L) ∈ S` using `fun x hx => ⟨x, hx, rfl⟩`. Establish `hS : ∀ a, c a ∈ S` using `fun a => memS ⟨c a, hR.const_mem a⟩ (A.algebraMap_mem a)`. Set `q : Ideal S` to `(IsLocalRing.maximalIdeal R).comap (Subring.inclusion hSR)`. Establish `unit_ne : ∀ t : R, IsUnit t → (t : L) ≠ 0`. Introduce `t ht h0`.

Take `⟨u, hu⟩` from `ht.exists_right_inv`. Use `congrArg (fun x : R => (x : L)) hu` as an intermediate fact. Simplify using `[h0] at this`. Use `⟨S, hS, q, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hA' : Algebra.FiniteType ℂ A` using `(Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset σ)`.

Set `e : A.toSubring ≃+* S` to `A.toSubring.equivMapOfInjective R.subtype Subtype.val_injective`. Establish `he : c.codRestrict S hS = (e.toRingHom : A →+* S).comp (algebraMap ℂ A)`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `h2 : (algebraMap ℂ A).FiniteType` using `RingHom.finiteType_algebraMap.mpr hA'`.

Rewrite using `[he]`. Conclude with `RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.surjective) h2`. Introduce `f`. Take `⟨r1, hr1, r2, hr2, hr20, e⟩` from `hR.frac f`. Take `⟨t1, ht1A, ht1, h1⟩` from `hσ ⟨r1, hr1⟩`.

Take `⟨t2, ht2A, ht2, h2⟩` from `hσ ⟨r2, hr2⟩`. Use `⟨r1 * t1 * t2, ?_, r2 * t2 * t1, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using memS _ (A.mul_mem h1 ht2A)`. Simplify using `using memS _ (A.mul_mem h2 ht1A)`. Conclude with `mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)`.

Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce `hf`.

Take `⟨t, htA, ht, h⟩` from `hσ ⟨f, hf⟩`. Use `⟨⟨_, memS _ h⟩, ⟨_, memS _ htA⟩, ?_, rfl⟩` and prove the remaining obligations. Introduce `hq`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hq ht`. Introduce and unpack `⟨a, b, hb, e⟩`.

Establish `hu : IsUnit (Subring.inclusion hSR b)`. Assume the negation of the conclusion as `h`. Conclude with `hb ((IsLocalRing.mem_maximalIdeal _).2 h)`. Take `⟨u, hu'⟩` from `hu.exists_right_inv`. Establish `hu'' : (b : L) * (u : L) = 1`.

Use `congrArg (fun x : R => (x : L)) hu'` as an intermediate fact. Simplify using `using this`. Establish `hf : f = a * u` using `by rw [← e, mul_assoc, hu'', mul_one]`. Rewrite using `[hf]`. Conclude with `R.mul_mem (hSR a.2) u.2`.
-/
theorem IsLocModel.exists_finiteType_localization :
    ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  intro L _ c R hR
  letI := hR.isLocalRing
  letI : Algebra ℂ R := (c.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  set A := Algebra.adjoin ℂ (σ : Set R) with hA
  let S : Subring L := A.toSubring.map R.subtype
  have hSR : S ≤ R := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have memS : ∀ x : R, x ∈ A → (x : L) ∈ S := fun x hx => ⟨x, hx, rfl⟩
  have hS : ∀ a, c a ∈ S := fun a => memS ⟨c a, hR.const_mem a⟩ (A.algebraMap_mem a)
  let q : Ideal S := (IsLocalRing.maximalIdeal R).comap (Subring.inclusion hSR)
  have unit_ne : ∀ t : R, IsUnit t → (t : L) ≠ 0 := by
    intro t ht h0
    obtain ⟨u, hu⟩ := ht.exists_right_inv
    have := congrArg (fun x : R => (x : L)) hu
    simp [h0] at this
  refine ⟨S, hS, q, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · have hA' : Algebra.FiniteType ℂ A :=
      (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset σ)
    let e : A.toSubring ≃+* S := A.toSubring.equivMapOfInjective R.subtype Subtype.val_injective
    have he : c.codRestrict S hS = (e.toRingHom : A →+* S).comp (algebraMap ℂ A) := by
      ext a; rfl
    have h2 : (algebraMap ℂ A).FiniteType := RingHom.finiteType_algebraMap.mpr hA'
    rw [he]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.surjective) h2
  · intro f
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hR.frac f
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    refine ⟨r1 * t1 * t2, ?_, r2 * t2 * t1, ?_, ?_, ?_⟩
    · simpa using memS _ (A.mul_mem h1 ht2A)
    · simpa using memS _ (A.mul_mem h2 ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring
  · intro f
    constructor
    · intro hf
      obtain ⟨t, htA, ht, h⟩ := hσ ⟨f, hf⟩
      refine ⟨⟨_, memS _ h⟩, ⟨_, memS _ htA⟩, ?_, rfl⟩
      intro hq
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · rintro ⟨a, b, hb, e⟩
      have hu : IsUnit (Subring.inclusion hSR b) := by
        by_contra h; exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu'⟩ := hu.exists_right_inv
      have hu'' : (b : L) * (u : L) = 1 := by
        have := congrArg (fun x : R => (x : L)) hu'; simpa using this
      have hf : f = a * u := by rw [← e, mul_assoc, hu'', mul_one]
      rw [hf]; exact R.mul_mem (hSR a.2) u.2

end GlobalTheory.FieldPair
