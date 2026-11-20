import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
open ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.ChartVal

/- English proof (translation)
Assume the negation of the conclusion as `hna`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hna isIntegral_zero`. Use `set B : Subring Ω := (Algebra.adjoin R {a⁻¹}).toSubring with hB`.

Establish `hbA : a⁻¹ ∈ B` using `Algebra.subset_adjoin rfl`. Establish `hnu : ¬ IsUnit (⟨a⁻¹, hbA⟩ : B)`. Introduce `hu`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `h1 : a⁻¹ * (w : Ω) = 1` using `congrArg Subtype.val hw`.

Establish `hwa : (w : Ω) = a`. Combine the equalities or inequalities in the displayed calculation. Establish `haA : a ∈ Algebra.adjoin R {a⁻¹}`. Establish `hw2` using `w.2`. Rewrite `hw2` using `[hwa]`.

Conclude with `hw2`. Apply `hna` to reduce the goal to its premises. Rewrite `haA` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, hp⟩` from `(AlgHom.mem_range _).mp haA`. Rewrite `hp` using `[Polynomial.aeval_def]`.

Use `letI : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha0)`. Establish `key` using `Polynomial.eval₂_reverse_mul_pow (algebraMap R Ω) a⁻¹ p`. Rewrite `key` using `[invOf_eq_inv, inv_inv, hp]`. Establish `hdeg : p.reverse.degree < ↑(p.natDegree + 1)`. Use `lt_of_le_of_lt Polynomial.degree_le_natDegree ?_` and prove the remaining obligations.

Conclude with `Nat.lt_succ_of_le (Polynomial.reverse_natDegree_le p)` after adjusting the coercions. Use `(show ∃ q : Polynomial R, q.Monic ∧ Polynomial.eval₂ (algebraMap R Ω) a q = 0 from ⟨Polynomial.X ^ (p.natDegree + 1) - p.reverse, Polynomial.monic_X_pow_sub hdeg, ?_⟩)` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`.

Use `_ = Polynomial.eval₂ (algebraMap R Ω) a p.reverse := by`. Rewrite using `[mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0, one_pow, mul_one]`. Take `⟨P, hP, hxP⟩` from `Ideal.exists_le_maximal (Ideal.span {(⟨a⁻¹, hbA⟩ : B)}) (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)`. Use `haveI := hP.isPrime`. Establish `hx : (⟨a⁻¹, hbA⟩ : B) ∈ P` using `hxP (Ideal.mem_span_singleton_self _)`.

Establish `hg : ∀ y : P.primeCompl, IsUnit (B.subtype (y : B))`. Introduce `y`. Use `isUnit_iff_ne_zero.mpr fun h => (show (y : B) ∉ P from y.2) ?_` and prove the remaining obligations. Establish `hy0 : (y : B) = 0` using `Subtype.ext h`. Rewrite using `[hy0]`.

Conclude with `P.zero_mem`. Set `f` to `IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hg`. Establish `hfl : ∀ z : B, f (algebraMap B (Localization.AtPrime P) z) = z` using `fun z => IsLocalization.lift_eq hg z`. Establish `hfinj : Function.Injective f`. Rewrite using `[IsLocalization.lift_injective_iff]`.

Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg f h`. Rewrite `h'` using `[hfl, hfl]`.

Conclude with `h'`. Introduce `h`. Establish `hxy : x = y` using `Subtype.ext h`. Rewrite using `[hxy]`. Take `⟨V, hV⟩` from `LocalSubring.exists_le_valuationSubring (LocalSubring.range f)`.

Take `⟨hle, hloc⟩` from `LocalSubring.le_def.mp hV`. Establish `hmemL : ∀ z : B, (z : Ω) ∈ (LocalSubring.range f).toSubring`. Introduce `z`. Use `first`. Consider the case `exact (show (z : Ω) ∈ Set.range f from ⟨_, hfl z⟩)`.

Consider the case `(rw [LocalSubring.range_toSubring]; exact ⟨_, hfl z⟩)`. Establish `haV : a ∈ V` using `H V fun r => hle (hmemL ⟨algebraMap R Ω r, Subalgebra.algebraMap_mem _ r⟩)`. Set `xL : (LocalSubring.range f).toSubring` to `⟨a⁻¹, hmemL ⟨a⁻¹, hbA⟩⟩`. Establish `hunitV : IsUnit (Subring.inclusion hle xL)` using `isUnit_iff_exists_inv.mpr ⟨⟨a, haV⟩, Subtype.ext (inv_mul_cancel₀ ha0)⟩`. Establish `hunitL : IsUnit xL` using `by first`.

Consider the case `exact isUnit_of_map_unit (Subring.inclusion hle) xL hunitV`. Consider the case `exact IsUnit.of_map (Subring.inclusion hle) xL hunitV`. Take `⟨w, hw⟩` from `hunitL.exists_right_inv`. Establish `hw2 : (w : Ω) ∈ Set.range f` using `w.2`. Take `⟨s, hs⟩` from `hw2`.

Establish `h1 : f (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩ * s) = f 1`. Rewrite using `[map_mul, hfl, hs, map_one]`. Conclude with `congrArg Subtype.val hw`. Establish `hu : IsUnit (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩)` using `isUnit_iff_exists_inv.mpr ⟨s, hfinj h1⟩`. Rewrite `hu` using `[IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P]`.

Conclude with `hu hx`.
-/
theorem isIntegral_of_forall_valuationSubring {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  classical
  by_contra hna
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hna isIntegral_zero
  set B : Subring Ω := (Algebra.adjoin R {a⁻¹}).toSubring with hB
  have hbA : a⁻¹ ∈ B := Algebra.subset_adjoin rfl
  have hnu : ¬ IsUnit (⟨a⁻¹, hbA⟩ : B) := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : a⁻¹ * (w : Ω) = 1 := congrArg Subtype.val hw
    have hwa : (w : Ω) = a := by
      calc (w : Ω) = a * (a⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        _ = a := by rw [h1, mul_one]
    have haA : a ∈ Algebra.adjoin R {a⁻¹} := by
      have hw2 := w.2
      rw [hwa] at hw2
      exact hw2
    apply hna
    rw [Algebra.adjoin_singleton_eq_range_aeval] at haA
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp haA
    rw [Polynomial.aeval_def] at hp
    letI : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha0)
    have key := Polynomial.eval₂_reverse_mul_pow (algebraMap R Ω) a⁻¹ p
    rw [invOf_eq_inv, inv_inv, hp] at key
    have hdeg : p.reverse.degree < ↑(p.natDegree + 1) := by
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast Nat.lt_succ_of_le (Polynomial.reverse_natDegree_le p)
    refine (show ∃ q : Polynomial R, q.Monic ∧ Polynomial.eval₂ (algebraMap R Ω) a q = 0 from
      ⟨Polynomial.X ^ (p.natDegree + 1) - p.reverse, Polynomial.monic_X_pow_sub hdeg, ?_⟩)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, sub_eq_zero]
    calc a ^ (p.natDegree + 1) = a * a ^ p.natDegree := pow_succ' a _
      _ = Polynomial.eval₂ (algebraMap R Ω) a p.reverse * a⁻¹ ^ p.natDegree * a ^ p.natDegree := by
          rw [key]
      _ = Polynomial.eval₂ (algebraMap R Ω) a p.reverse := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0, one_pow, mul_one]
  obtain ⟨P, hP, hxP⟩ := Ideal.exists_le_maximal (Ideal.span {(⟨a⁻¹, hbA⟩ : B)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)
  haveI := hP.isPrime
  have hx : (⟨a⁻¹, hbA⟩ : B) ∈ P := hxP (Ideal.mem_span_singleton_self _)
  have hg : ∀ y : P.primeCompl, IsUnit (B.subtype (y : B)) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => (show (y : B) ∉ P from y.2) ?_
    have hy0 : (y : B) = 0 := Subtype.ext h
    rw [hy0]
    exact P.zero_mem
  let f := IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hg
  have hfl : ∀ z : B, f (algebraMap B (Localization.AtPrime P) z) = z := fun z =>
    IsLocalization.lift_eq hg z
  have hfinj : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have h' := congrArg f h
      rw [hfl, hfl] at h'
      exact h'
    · intro h
      have hxy : x = y := Subtype.ext h
      rw [hxy]
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have hmemL : ∀ z : B, (z : Ω) ∈ (LocalSubring.range f).toSubring := by
    intro z
    first
      | exact (show (z : Ω) ∈ Set.range f from ⟨_, hfl z⟩)
      | (rw [LocalSubring.range_toSubring]; exact ⟨_, hfl z⟩)
  have haV : a ∈ V := H V fun r => hle (hmemL ⟨algebraMap R Ω r, Subalgebra.algebraMap_mem _ r⟩)
  let xL : (LocalSubring.range f).toSubring := ⟨a⁻¹, hmemL ⟨a⁻¹, hbA⟩⟩
  have hunitV : IsUnit (Subring.inclusion hle xL) :=
    isUnit_iff_exists_inv.mpr ⟨⟨a, haV⟩, Subtype.ext (inv_mul_cancel₀ ha0)⟩
  have hunitL : IsUnit xL := by
    first
      | exact isUnit_of_map_unit (Subring.inclusion hle) xL hunitV
      | exact IsUnit.of_map (Subring.inclusion hle) xL hunitV
  obtain ⟨w, hw⟩ := hunitL.exists_right_inv
  have hw2 : (w : Ω) ∈ Set.range f := w.2
  obtain ⟨s, hs⟩ := hw2
  have h1 : f (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩ * s) = f 1 := by
    rw [map_mul, hfl, hs, map_one]
    exact congrArg Subtype.val hw
  have hu : IsUnit (algebraMap B (Localization.AtPrime P) ⟨a⁻¹, hbA⟩) :=
    isUnit_iff_exists_inv.mpr ⟨s, hfinj h1⟩
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at hu
  exact hu hx

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a u q x H c hc`. Establish `e : x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) = x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q`. Rewrite using `[mul_pow, ← Finset.prod_pow, mul_assoc]`. Use `congr 2`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `show x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω`. Rewrite using `[e, mem_integralClosure_iff]`.

Use `isIntegral_of_forall_valuationSubring Subtype.val_injective _ fun V hV => H c hc V fun p => ?_` and prove the remaining obligations. Conclude with `hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩`.
-/
theorem mem_chartLatNm_of_forall_valuationSubring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω),
    (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω,
      (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) →
    x * u ^ q ∈ chartLatNm y a q := by
  intro K _ ι _ Ω _ y a u q x H c hc
  have e : x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) =
      x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q := by
    rw [mul_pow, ← Finset.prod_pow, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  show x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω
  rw [e, mem_integralClosure_iff]
  refine isIntegral_of_forall_valuationSubring Subtype.val_injective _ fun V hV => H c hc V fun p => ?_
  exact hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.ChartVal
