import Mathlib

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

section krull

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]

/- English proof (translation)
Establish `hx : IsIntegral F x` using `Algebra.IsIntegral.isIntegral x`. Use `haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) := IntermediateField.adjoin.finiteDimensional hx`. Establish `hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `τ hτ`.

Use `⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Establish `hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup` using `hσ`. Rewrite `hσ'` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `h1` using `hσ' x (IntermediateField.mem_adjoin_simple_self F x)`.

Establish `h2 : σ x = τ x`. Combine the equalities or inequalities in the displayed calculation. Use `show P (σ x)`. Rewrite using `[h2]`. Conclude with `hτ`.

Conclude with `hH.preimage (continuous_const.mul continuous_id)`. Use `show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`.
-/
theorem isOpen_setOf_apply (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
    have h1 := hσ' x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : σ x = τ x := by
      calc σ x = (τ * (τ⁻¹ * σ)) x := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) x) := by rw [AlgEquiv.mul_apply]
        _ = τ x := by rw [h1]
    show P (σ x)
    rw [h2]
    exact hτ
  · exact hH.preimage (continuous_const.mul continuous_id)
  · show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff]`. Conclude with `isOpen_setOf_apply x (fun y => ¬ P y)`.
-/
theorem isClosed_setOf_apply (x : Ω) (P : Ω → Prop) : IsClosed {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_apply x (fun y => ¬ P y)

end krull

section roots

variable {Ω : Type*} [Field Ω]

/- English proof (translation)
Establish `hξ1 : A.valuation ξ ≤ 1`. Establish `h2` using `Valuation.map_add A.valuation (ξ - 1) 1`. Rewrite `h2` using `[sub_add_cancel, Valuation.map_one]`. Conclude with `h2.trans (max_le h.le le_rfl)`. Establish `hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1` using `fun j => by`.

Rewrite using `[Valuation.map_pow]`. Conclude with `pow_le_one' hξ1 j`. Establish `hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1`. Introduce `i`. Rewrite using `[← geom_sum_mul, Valuation.map_mul]`.

Use `lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h` and prove the remaining obligations. Conclude with `Valuation.map_sum_le _ (fun j _ => hpow j)`. Assume the negation of the conclusion as `hne`. Establish `h3` using `geom_sum_mul ξ N`. Rewrite `h3` using `[hξ, sub_self]`.

Establish `hS` using `(mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))`. Establish `h5` using `Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1) one_ne_zero (fun i _ => hgeom i)`. Rewrite `h5` using `[Finset.sum_sub_distrib, hS]`. Apply `hN` to reduce the goal to its premises. Simplify using `using h5`.
-/
theorem eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  have hξ1 : A.valuation ξ ≤ 1 := by
    have h2 := Valuation.map_add A.valuation (ξ - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h2
    exact h2.trans (max_le h.le le_rfl)
  have hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1 := fun j => by
    rw [Valuation.map_pow]
    exact pow_le_one' hξ1 j
  have hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
    intro i
    rw [← geom_sum_mul, Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h
    exact Valuation.map_sum_le _ (fun j _ => hpow j)
  by_contra hne
  have h3 := geom_sum_mul ξ N
  rw [hξ, sub_self] at h3
  have hS := (mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))
  have h5 := Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1)
    one_ne_zero (fun i _ => hgeom i)
  rw [Finset.sum_sub_distrib, hS] at h5
  apply hN
  simpa using h5

/- English proof (translation)
Establish `h1 : A.valuation b ^ N = 1` using `by rw [← Valuation.map_pow, hb, Valuation.map_one]`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `Nat.exists_eq_succ_of_ne_zero hN0`. Rewrite `h1` using `[pow_succ]`. Break down `lt_trichotomy (A.valuation b) 1 with hlt | heq | hgt` into its components or cases. It suffices to derive a contradiction.

Establish `h2 : A.valuation b ^ M * A.valuation b ≤ A.valuation b` using `mul_le_of_le_one_left' (pow_le_one' hlt.le M)`. Rewrite `h2` using `[h1]`. Conclude with `absurd hlt (not_lt.2 h2)`. Conclude with `heq`. It suffices to derive a contradiction.

Establish `h2 : A.valuation b ≤ A.valuation b ^ M * A.valuation b` using `le_mul_of_one_le_left' (one_le_pow_of_one_le' hgt.le M)`. Rewrite `h2` using `[h1]`. Conclude with `absurd hgt (not_lt.2 h2)`.
-/
theorem valuation_eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN0 : N ≠ 0) {b : Ω}
    (hb : b ^ N = 1) : A.valuation b = 1 := by
  have h1 : A.valuation b ^ N = 1 := by rw [← Valuation.map_pow, hb, Valuation.map_one]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  rw [pow_succ] at h1
  rcases lt_trichotomy (A.valuation b) 1 with hlt | heq | hgt
  · exfalso
    have h2 : A.valuation b ^ M * A.valuation b ≤ A.valuation b :=
      mul_le_of_le_one_left' (pow_le_one' hlt.le M)
    rw [h1] at h2
    exact absurd hlt (not_lt.2 h2)
  · exact heq
  · exfalso
    have h2 : A.valuation b ≤ A.valuation b ^ M * A.valuation b :=
      le_mul_of_one_le_left' (one_le_pow_of_one_le' hgt.le M)
    rw [h1] at h2
    exact absurd hgt (not_lt.2 h2)

/- English proof (translation)
Establish `hN0 : N ≠ 0`. Introduce and unpack `rfl`. Apply `hN` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `hb0 : b ≠ 0`.

Introduce and unpack `rfl`. Simplify using `[hN0] at hb`. Establish `hvb` using `valuation_eq_one_of_pow_eq_one A hN0 hb`. Establish `hξ : (a / b) ^ N = 1` using `by rw [div_pow, ha, hb, div_one]`. Establish `hξ1 : A.valuation (a / b - 1) < 1`.

Rewrite using `[div_sub_one hb0, Valuation.map_div, hvb, div_one]`. Conclude with `h`. Establish `h2` using `eq_one_of_pow_eq_one A hN hξ hξ1`. Rewrite `h2` using `[div_eq_one_iff_eq hb0]`. Then use the resulting hypothesis.
-/
theorem eq_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    apply hN
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [hN0] at hb
  have hvb := valuation_eq_one_of_pow_eq_one A hN0 hb
  have hξ : (a / b) ^ N = 1 := by rw [div_pow, ha, hb, div_one]
  have hξ1 : A.valuation (a / b - 1) < 1 := by
    rw [div_sub_one hb0, Valuation.map_div, hvb, div_one]
    exact h
  have h2 := eq_one_of_pow_eq_one A hN hξ hξ1
  rwa [div_eq_one_iff_eq hb0] at h2

end roots

section exists_place

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/- English proof (translation)
Set `φ : 𝓞 F →+* Ω` to `(algebraMap F Ω).comp (algebraMap (𝓞 F) F)`. Establish `hφ : Function.Injective φ` using `(algebraMap F Ω).injective.comp (IsFractionRing.injective (𝓞 F) F)`. Establish `hu : ∀ y : v.asIdeal.primeCompl, IsUnit (φ y)`. Introduce `y`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations.

Introduce `h0`. Apply `y.2` to reduce the goal to its premises. Establish `h1 : (y : 𝓞 F) = 0` using `hφ (h0.trans (map_zero φ).symm)`. Rewrite using `[h1]`. Conclude with `v.asIdeal.zero_mem`.

Set `f : (Localization.AtPrime v.asIdeal) →+* Ω` to `IsLocalization.lift (M := v.asIdeal.primeCompl) hu`. Establish `hf : ∀ z : 𝓞 F, f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) z) = φ z` using `fun z => IsLocalization.lift_eq hu z`. Establish `hfi : Function.Injective f`. Rewrite using `[IsLocalization.lift_injective_iff]`. Introduce `a b`.

Prove the components needed by the constructor for the conclusion. Introduce `hab`. Rewrite using `[IsLocalization.injective (M := v.asIdeal.primeCompl) (S := (Localization.AtPrime v.asIdeal)) (Ideal.primeCompl_le_nonZeroDivisors _) hab]`. Introduce `hab`. Rewrite using `[hφ hab]`.

Take `⟨B, hB⟩` from `LocalSubring.exists_le_valuationSubring (LocalSubring.range f)`. Rewrite `hB` using `[LocalSubring.le_def]`. Take `⟨hle, hloc⟩` from `hB`. Use `haveI := hloc`. Use `⟨B, fun x => ?_⟩` and prove the remaining obligations.

Establish `hmem : φ x ∈ B` using `hle ⟨algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x, hf x⟩`. Set `bx : B` to `⟨φ x, hmem⟩`. Establish `hv : B.valuation (algebraMap F Ω (x : F)) = B.valuation (bx : Ω)` using `rfl`. Rewrite using `[hv, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hnu`. Assume the negation of the conclusion as `hx`. Apply `hnu` to reduce the goal to its premises. Establish `h1 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x)` using `IsLocalization.map_units (Localization.AtPrime v.asIdeal) (⟨x, hx⟩ : v.asIdeal.primeCompl)`. Establish `h3` using `(h1.map f.rangeRestrict).map (Subring.inclusion hle)`.

Rewrite `h3` using `[show f.rangeRestrict (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) = (⟨φ x, ⟨_, hf x⟩⟩ : f.range) from Subtype.ext (hf x)]`. Conclude with `h3`. Introduce `hx hu'`. Establish `h1` using `isUnit_of_map_unit (Subring.inclusion hle) ⟨φ x, ⟨_, hf x⟩⟩ hu'`. Take `⟨w, hw⟩` from `h1.exists_right_inv`.

Take `⟨r, hr⟩` from `w.2`. Establish `h4 : f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x * r) = f 1`. Rewrite using `[map_mul, hf, hr, map_one]`. Conclude with `congrArg Subtype.val hw`. Establish `h5 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x)` using `⟨⟨_, r, hfi h4, (mul_comm _ _).trans (hfi h4)⟩, rfl⟩`.

Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal x).1 h5 hx`.
-/
theorem exists_valuationSubring_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring Ω, ∀ x : 𝓞 F,
      A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  classical
  let φ : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hφ : Function.Injective φ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hu : ∀ y : v.asIdeal.primeCompl, IsUnit (φ y) := by
    intro y
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply y.2
    have h1 : (y : 𝓞 F) = 0 := hφ (h0.trans (map_zero φ).symm)
    rw [h1]
    exact v.asIdeal.zero_mem
  let f : (Localization.AtPrime v.asIdeal) →+* Ω := IsLocalization.lift (M := v.asIdeal.primeCompl) hu
  have hf : ∀ z : 𝓞 F, f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) z) = φ z := fun z => IsLocalization.lift_eq hu z
  have hfi : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      rw [IsLocalization.injective (M := v.asIdeal.primeCompl) (S := (Localization.AtPrime v.asIdeal))
        (Ideal.primeCompl_le_nonZeroDivisors _) hab]
    · intro hab
      rw [hφ hab]
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  rw [LocalSubring.le_def] at hB
  obtain ⟨hle, hloc⟩ := hB
  haveI := hloc
  refine ⟨B, fun x => ?_⟩
  have hmem : φ x ∈ B := hle ⟨algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x, hf x⟩
  let bx : B := ⟨φ x, hmem⟩
  have hv : B.valuation (algebraMap F Ω (x : F)) = B.valuation (bx : Ω) := rfl
  rw [hv, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hx
    apply hnu
    have h1 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) :=
      IsLocalization.map_units (Localization.AtPrime v.asIdeal) (⟨x, hx⟩ : v.asIdeal.primeCompl)
    have h3 := (h1.map f.rangeRestrict).map (Subring.inclusion hle)
    rw [show f.rangeRestrict (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) =
      (⟨φ x, ⟨_, hf x⟩⟩ : f.range) from Subtype.ext (hf x)] at h3
    exact h3
  · intro hx hu'
    have h1 := isUnit_of_map_unit (Subring.inclusion hle) ⟨φ x, ⟨_, hf x⟩⟩ hu'
    obtain ⟨w, hw⟩ := h1.exists_right_inv
    obtain ⟨r, hr⟩ := w.2
    have h4 : f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x * r) = f 1 := by
      rw [map_mul, hf, hr, map_one]
      exact congrArg Subtype.val hw
    have h5 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) := ⟨⟨_, r, hfi h4, (mul_comm _ _).trans (hfi h4)⟩, rfl⟩
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal x).1 h5 hx

end exists_place

end ReciprocityTheory.Gal
