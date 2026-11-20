import Mathlib

open IsLocalRing

namespace GlobalTheory.PrimeElement

variable {R : Type*} [CommRing R] {π : R}

/- English proof (translation)
The claim follows from `(Ideal.span_singleton_prime hπ.ne_zero).2 hπ`.
-/
theorem isPrime_span (hπ : Prime π) : (Ideal.span {π}).IsPrime :=
  (Ideal.span_singleton_prime hπ.ne_zero).2 hπ

/- English proof (translation)
Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]`.
-/
theorem mem_primeCompl_span [(Ideal.span {π}).IsPrime] {b : R} :
    b ∈ (Ideal.span {π}).primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `FiniteMultiplicity.of_not_isUnit hπ h`. Conclude with `hn (hx _)`.
-/
theorem eq_zero_of_forall_pow_dvd [IsDomain R] [IsNoetherianRing R] (hπ : ¬ IsUnit π) {x : R}
    (hx : ∀ e : ℕ, π ^ e ∣ x) : x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hπ h
  exact hn (hx _)

section AtPrime

variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

/- English proof (translation)
Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span, Set.image_singleton]`.
-/
theorem maximalIdeal_eq_span [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span,
    Set.image_singleton]

/- English proof (translation)
Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff S (Ideal.span {π}), mem_primeCompl_span]`.
-/
theorem isUnit_algebraMap_iff (x : R) : IsUnit (algebraMap R S x) ↔ ¬ π ∣ x := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff S (Ideal.span {π}), mem_primeCompl_span]

include π in
/- English proof (translation)
The claim follows from `IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors`.
-/
theorem algebraMap_atPrime_injective [IsDomain R] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

include π in
/- English proof (translation)
The claim follows from `IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors`.
-/
theorem isDomain_atPrime [IsDomain R] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

/- English proof (translation)
Use `IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})` as an intermediate fact. Establish `: IsNoetherianRing S` using `IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance`. Establish `hne : algebraMap R S π ≠ 0` using `(map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ`. Establish `hf : ¬ IsField S`. Rewrite using `[isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]`.

Conclude with `hne`. Use `((IsDiscreteValuationRing.TFAE S hf).out 0 4).2 ?_` and prove the remaining obligations. Conclude with `⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩`.
-/
theorem isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance
  have hne : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ
  have hf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]
    exact hne
  refine ((IsDiscreteValuationRing.TFAE S hf).out 0 4).2 ?_
  exact ⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩

/- English proof (translation)
Use `isDomain_atPrime (π := π) S` as an intermediate fact. Use `isDiscreteValuationRing (π := π) S hπ` as an intermediate fact. Conclude with `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)`.
-/
theorem irreducible_algebraMap [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by
  have := isDomain_atPrime (π := π) S
  have := isDiscreteValuationRing (π := π) S hπ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)

end AtPrime

/- English proof (translation)
Establish `hinj` using `FaithfulSMul.algebraMap_injective R K`. Use `hinj.isDomain` as an intermediate fact. Establish `h : b * a = π ^ n * c` using `hinj <| by`. Rewrite using `[map_mul, map_mul, ← ha, ← hc]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, rfl⟩ : π ^ n ∣ a` from `hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩`. Use `⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩` and prove the remaining obligations. Rewrite using `[ha, map_mul]`.
-/
theorem exists_eq_of_pow_mul_of_mul {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    [FaithfulSMul R K] (hπ : Prime π) {x : K} {n : ℕ} {a b c : R}
    (ha : algebraMap R K (π ^ n) * x = algebraMap R K a) (hb : ¬ π ∣ b)
    (hc : algebraMap R K b * x = algebraMap R K c) : ∃ r : R, algebraMap R K r = x := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have := hinj.isDomain
  have h : b * a = π ^ n * c := hinj <| by
    rw [map_mul, map_mul, ← ha, ← hc]; ring
  obtain ⟨r, rfl⟩ : π ^ n ∣ a := hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩
  refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩
  rw [ha, map_mul]

section Inter

variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]

/- English proof (translation)
Establish `hp : Prime π` using `(Ideal.span_singleton_prime hπ).1 inferInstance`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩`. Take `⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩` from `IsLocalization.surj (Submonoid.powers π) y`. Take `⟨⟨c, ⟨b, hb⟩⟩, h₂⟩` from `IsLocalization.surj (Ideal.span {π}).primeCompl z`.

Use `exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_ (mem_primeCompl_span.1 hb) ?_` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁, map_mul, hy, mul_comm]`. Rewrite using `[IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂, map_mul, hz, mul_comm]`. Introduce and unpack `_ ⟨r, rfl⟩`. Conclude with `⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩, ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩`.
-/
theorem range_inf_range (hπ : π ≠ 0) :
    (algebraMap A K).range ⊓ (algebraMap S K).range = (algebraMap R K).range := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers π) y
    obtain ⟨⟨c, ⟨b, hb⟩⟩, h₂⟩ := IsLocalization.surj (Ideal.span {π}).primeCompl z
    refine exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_
      (mem_primeCompl_span.1 hb) ?_
    · rw [IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁,
        map_mul, hy, mul_comm]
    · rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂,
        map_mul, hz, mul_comm]
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩,
      ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩

omit [(Ideal.span {π}).IsPrime] in
/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `hinj` using `FaithfulSMul.algebraMap_injective R K`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers π) y`. Establish `h` using `congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)`.

Rewrite `h` using `[map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm, map_eq_zero_iff _ hinj]`. Simplify using `[h]`.
-/
theorem algebraMap_away_injective (hπ : π ≠ 0) : Function.Injective (algebraMap A K) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hinj := FaithfulSMul.algebraMap_injective R K
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers π) y
  have h := congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)
  rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm,
    map_eq_zero_iff _ hinj] at h
  simp [h]

variable {A S} in

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : algebraMap A K y ∈ (algebraMap R K).range := by`. Rewrite using `[← range_inf_range A S K hπ]`. Conclude with `⟨⟨y, rfl⟩, ⟨z, h.symm⟩⟩`. Conclude with `⟨r, algebraMap_away_injective A K hπ (by rw [← IsScalarTower.algebraMap_apply, hr])⟩`.
-/
theorem exists_algebraMap_eq (hπ : π ≠ 0) {y : A} {z : S}
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, algebraMap R A r = y := by
  obtain ⟨r, hr⟩ : algebraMap A K y ∈ (algebraMap R K).range := by
    rw [← range_inf_range A S K hπ]
    exact ⟨⟨y, rfl⟩, ⟨z, h.symm⟩⟩
  exact ⟨r, algebraMap_away_injective A K hπ (by rw [← IsScalarTower.algebraMap_apply, hr])⟩

variable {A S} in

/- English proof (translation)
Take `⟨y, rfl⟩` from `hy`. Take `⟨z, rfl⟩` from `hz`. Establish `h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ)`. Use `mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]`.

Take `⟨r, hr⟩` from `exists_algebraMap_eq K hπ h`. Take `⟨r', hr'⟩` from `exists_algebraMap_eq K hπ h'`. Use `⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]`.
-/
theorem exists_unit_algebraMap_eq (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  have h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ) := by
    refine mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_
    rw [← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨r, hr⟩ := exists_algebraMap_eq K hπ h
  obtain ⟨r', hr'⟩ := exists_algebraMap_eq K hπ h'
  refine ⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩
  rw [IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]

end Inter

section Valuation

variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]

/- English proof (translation)
Take `⟨z, hz⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one h.le`. Use `exists_unit_algebraMap_eq K hπ hy (z := z) ?_ hz.symm` and prove the remaining obligations. Rewrite `h` using `[← hz, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]`. Conclude with `notMem_maximalIdeal.1 h`.
-/
theorem exists_unit_algebraMap_eq_of_valuation_eq_one (hπ : π ≠ 0) {y : A} (hy : IsUnit y)
    (h : (IsDiscreteValuationRing.maximalIdeal S).valuation K (algebraMap A K y) = 1) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
  refine exists_unit_algebraMap_eq K hπ hy (z := z) ?_ hz.symm
  rw [← hz, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem] at h
  exact notMem_maximalIdeal.1 h

end Valuation

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective S K`. Establish `h0 : algebraMap S K ϖ ≠ 0` using `(map_ne_zero_iff _ hinj).2 hϖ.ne_zero`. Establish `key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x → algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a`. Introduce `a b u v hv h₁ h₂`. Use `by_contra! hlt`.

Take `⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ)` from `⟨(b - a - 1).toNat, by push_cast; omega⟩`. Establish `: v = ϖ * (ϖ ^ n * u)` using `hinj <| by`. Rewrite using `[h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))`.

Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := S) x`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hp0 : p ≠ 0` using `by rintro rfl; simp at hx`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ`.

Use `existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_` and prove the remaining obligations. Establish `hv : algebraMap S K v ≠ 0` using `(v.isUnit.map _).ne_zero`. Rewrite using `[zpow_sub₀ h0]`. Simplify using `only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Introduce and unpack `a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩`. Conclude with `le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)`.
-/
theorem existsUnique_zpow_mul_eq_unit {S K : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] {ϖ : S}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃! a : ℤ, ∃ u : S, IsUnit u ∧ algebraMap S K u = algebraMap S K ϖ ^ a * x := by
  have hinj := IsFractionRing.injective S K
  have h0 : algebraMap S K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x →
      algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a := by
    intro a b u v hv h₁ h₂
    by_contra! hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
    have : v = ϖ * (ϖ ^ n * u) := hinj <| by
      rw [h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_
  · have hv : algebraMap S K v ≠ 0 := (v.isUnit.map _).ne_zero
    rw [zpow_sub₀ h0]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]
    field_simp
  · rintro a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩
    exact le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)

end GlobalTheory.PrimeElement
