import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.GatR

open QuadraticAlgebra IsLocalRing

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}

/- English proof (translation)
Apply the tactic sequence `rw [sq, algebraMap_eq]; ext <;> simp`.
-/
theorem om_sq : (ω : QuadraticAlgebra W ϖ 0) ^ 2 = algebraMap W _ ϖ := by
  rw [sq, algebraMap_eq]; ext <;> simp

/- English proof (translation)
Rewrite using `[pow_mul, om_sq, map_pow]`.
-/
theorem om_pow (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = algebraMap W _ (ϖ ^ n) := by
  rw [pow_mul, om_sq, map_pow]

/- English proof (translation)
Rewrite using `[isUnit_iff_norm_isUnit, norm_def]`. Assume the negation of the conclusion as `hn`. Establish `h1 : ϖ * z.im * z.im ∈ nonunits W` using `fun hu => hϖ.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))`. Establish `h2` using `nonunits_add (show _ ∈ nonunits W from hn) h1`. Establish `e : z.re * z.re + 0 * z.re * z.im - ϖ * z.im * z.im + ϖ * z.im * z.im = z.re * z.re` using `by ring`.

Rewrite `h2` using `[e]`. Conclude with `h2 (h.mul h)`.
-/
theorem isUnit_of_re (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (h : IsUnit z.re) : IsUnit z := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  by_contra hn
  have h1 : ϖ * z.im * z.im ∈ nonunits W := fun hu =>
    hϖ.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  have h2 := nonunits_add (show _ ∈ nonunits W from hn) h1
  have e : z.re * z.re + 0 * z.re * z.im - ϖ * z.im * z.im + ϖ * z.im * z.im = z.re * z.re := by ring
  rw [e] at h2
  exact h2 (h.mul h)

/- English proof (translation)
Rewrite using `[isUnit_iff_norm_isUnit, norm_def]`. Simplify using `only [omega_re, omega_im]`. Introduce `h`. Establish `e : (0 : W) * 0 + 0 * 0 * 1 - ϖ * 1 * 1 = -ϖ` using `by ring`. Rewrite `h` using `[e, IsUnit.neg_iff]`.

Conclude with `hϖ.not_isUnit h`.
-/
theorem om_not_isUnit (hϖ : Irreducible ϖ) : ¬ IsUnit (ω : QuadraticAlgebra W ϖ 0) := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  simp only [omega_re, omega_im]
  intro h
  have e : (0 : W) * 0 + 0 * 0 * 1 - ϖ * 1 * 1 = -ϖ := by ring
  rw [e, IsUnit.neg_iff] at h
  exact hϖ.not_isUnit h

/- English proof (translation)
Establish `caseB : ∀ (j : ℕ) (v : Wˣ) (a' : W), z.im = v * ϖ ^ j → z.re = ϖ ^ (j + 1) * a' → ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u` using `fun j v a' h1 h2 => by`. Use `⟨2 * j + 1, ⟨v, a'⟩, isUnit_of_re hϖ _ v.isUnit, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, om_pow, algebraMap_eq]`. Use `ext`. Simplify using `only [re_mul, im_mul, omega_re, omega_im, h2]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [re_mul, im_mul, omega_re, omega_im, h1]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `ha : z.re = 0`. Apply the tactic sequence `have hb : z.im ≠ 0 := fun hb => hz (by ext <;> simp [ha, hb])`.

Take `⟨j, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ`. Conclude with `caseB j v 0 hv (by rw [ha, mul_zero])`. Take `⟨i, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Distinguish the cases in `hd : ϖ ^ i ∣ z.im`. Take `⟨b', hb'⟩` from `hd`.

Use `⟨2 * i, ⟨u, b'⟩, isUnit_of_re hϖ _ u.isUnit, ?_⟩` and prove the remaining obligations. Rewrite using `[om_pow, algebraMap_eq]`. Use `ext`. Simplify using `[hu]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hb']`. Establish `hb : z.im ≠ 0` using `fun hb => hd (by rw [hb]; exact dvd_zero _)`. Take `⟨j, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ`. Establish `hji : j < i`. Assume the negation of the conclusion as `hc`.

Conclude with `hd (hv ▸ Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hc)) _)`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_lt hji`. Conclude with `caseB j v (u * ϖ ^ c) hv (by rw [hu]; ring)`.
-/
theorem fact (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (hz : z ≠ 0) :
    ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := by
  have caseB : ∀ (j : ℕ) (v : Wˣ) (a' : W), z.im = v * ϖ ^ j → z.re = ϖ ^ (j + 1) * a' →
      ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := fun j v a' h1 h2 => by
    refine ⟨2 * j + 1, ⟨v, a'⟩, isUnit_of_re hϖ _ v.isUnit, ?_⟩
    rw [pow_succ, om_pow, algebraMap_eq]
    ext
    · simp only [re_mul, im_mul, omega_re, omega_im, h2]; ring
    · simp only [re_mul, im_mul, omega_re, omega_im, h1]; ring
  by_cases ha : z.re = 0
  · have hb : z.im ≠ 0 := fun hb => hz (by ext <;> simp [ha, hb])
    obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    exact caseB j v 0 hv (by rw [ha, mul_zero])
  · obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    by_cases hd : ϖ ^ i ∣ z.im
    · obtain ⟨b', hb'⟩ := hd
      refine ⟨2 * i, ⟨u, b'⟩, isUnit_of_re hϖ _ u.isUnit, ?_⟩
      rw [om_pow, algebraMap_eq]
      ext
      · simp [hu]; ring
      · simp [hb']
    · have hb : z.im ≠ 0 := fun hb => hd (by rw [hb]; exact dvd_zero _)
      obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      have hji : j < i := by
        by_contra hc
        exact hd (hv ▸ Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hc)) _)
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hji
      exact caseB j v (u * ϖ ^ c) hv (by rw [hu]; ring)

/- English proof (translation)
Introduce `h`. Establish `h2 : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = 0` using `by rw [two_mul, pow_add, h, mul_zero]`. Rewrite `h2` using `[om_pow, map_eq_zero_iff _ algebraMap_injective]`. Conclude with `pow_ne_zero n hϖ.ne_zero h2`.
-/
theorem om_pow_ne_zero (hϖ : Irreducible ϖ) (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ n ≠ 0 := by
  intro h
  have h2 : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = 0 := by rw [two_mul, pow_add, h, mul_zero]
  rw [om_pow, map_eq_zero_iff _ algebraMap_injective] at h2
  exact pow_ne_zero n hϖ.ne_zero h2

/- English proof (translation)
Establish `: NoZeroDivisors (QuadraticAlgebra W ϖ 0)` using `⟨fun {x y} hxy => by`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or]`. Take `⟨n, u, hu, rfl⟩` from `fact hϖ x hc.1`. Take `⟨m, v, hv, rfl⟩` from `fact hϖ y hc.2`.

Establish `e : ω ^ n * u * (ω ^ m * v) = ω ^ (n + m) * (u * v)` using `by ring`. Rewrite `hxy` using `[e]`. Conclude with `om_pow_ne_zero hϖ (n + m) ((hu.mul hv).mul_left_eq_zero.mp hxy)⟩`. Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem isDomain (hϖ : Irreducible ϖ) : IsDomain (QuadraticAlgebra W ϖ 0) := by
  have : NoZeroDivisors (QuadraticAlgebra W ϖ 0) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hc.1
    obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hc.2
    have e : ω ^ n * u * (ω ^ m * v) = ω ^ (n + m) * (u * v) := by ring
    rw [e] at hxy
    exact om_pow_ne_zero hϖ (n + m) ((hu.mul hv).mul_left_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain _

/- English proof (translation)
Use `isDomain hϖ` as an intermediate fact. Use `⟨om_not_isUnit hϖ, fun x y hxy => ?_⟩` and prove the remaining obligations. Establish `h0 : (ω : QuadraticAlgebra W ϖ 0) ≠ 0` using `by simpa using om_pow_ne_zero hϖ 1`. Establish `hx : x ≠ 0` using `fun h => h0 (by rw [hxy, h, zero_mul])`. Establish `hy : y ≠ 0` using `fun h => h0 (by rw [hxy, h, mul_zero])`.

Take `⟨n, u, hu, rfl⟩` from `fact hϖ x hx`. Take `⟨m, v, hv, rfl⟩` from `fact hϖ y hy`. Break down `n with _ | n` into its components or cases. Use `left`. Simplify using `using hu`.

Break down `m with _ | m` into its components or cases. Use `right`. Simplify using `using hv`. It suffices to derive a contradiction. Establish `e : (ω : QuadraticAlgebra W ϖ 0) * 1 = ω * (ω * (ω ^ (n + m) * (u * v)))`.

Rewrite using `[mul_one]`. Use `conv_lhs => rw [hxy]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `om_not_isUnit hϖ (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ h0 e).symm)`.
-/
theorem om_irreducible (hϖ : Irreducible ϖ) : Irreducible (ω : QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine ⟨om_not_isUnit hϖ, fun x y hxy => ?_⟩
  have h0 : (ω : QuadraticAlgebra W ϖ 0) ≠ 0 := by simpa using om_pow_ne_zero hϖ 1
  have hx : x ≠ 0 := fun h => h0 (by rw [hxy, h, zero_mul])
  have hy : y ≠ 0 := fun h => h0 (by rw [hxy, h, mul_zero])
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hy
  rcases n with _ | n
  · left; simpa using hu
  rcases m with _ | m
  · right; simpa using hv
  exfalso
  have e : (ω : QuadraticAlgebra W ϖ 0) * 1 = ω * (ω * (ω ^ (n + m) * (u * v))) := by
    rw [mul_one]; conv_lhs => rw [hxy]
    ring
  exact om_not_isUnit hϖ (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ h0 e).symm)

/- English proof (translation)
The claim follows from `isDomain hϖ; IsDiscreteValuationRing (QuadraticAlgebra W ϖ 0) := by have := isDomain hϖ refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ω, om_irreducible hϖ, fun {x} hx => ?_⟩ obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx exact ⟨n, hu.unit, rfl⟩`.
-/
theorem isDVR (hϖ : Irreducible ϖ) :
    haveI := isDomain hϖ; IsDiscreteValuationRing (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ω, om_irreducible hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  exact ⟨n, hu.unit, rfl⟩

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton, om_pow, algebraMap_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨⟨t.re, by simp⟩, ⟨t.im, by simp⟩⟩`. Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`.

Apply the tactic sequence `exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩`.
-/
theorem mem_span_om_pow (m : ℕ) (z : QuadraticAlgebra W ϖ 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} ↔ ϖ ^ m ∣ z.re ∧ ϖ ^ m ∣ z.im := by
  rw [Ideal.mem_span_singleton, om_pow, algebraMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t.re, by simp⟩, ⟨t.im, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩

/- English proof (translation)
The claim follows from `isDomain hϖ; haveI := isDVR hϖ IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by have := isDomain hϖ have := isDVR hϖ have keyO : ∀ (n : ℕ) (x y : QuadraticAlgebra W ϖ 0), x ≡ y [SMOD (maximalIdeal (QuadraticAlgebra W ϖ 0) ^ n • ⊤ : Submodule _ …`.
-/
theorem isAdicComplete (hϖ : Irreducible ϖ) (hC : IsAdicComplete (Ideal.span {ϖ}) W) :
    haveI := isDomain hϖ; haveI := isDVR hϖ
    IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  have := isDVR hϖ
  have keyO : ∀ (n : ℕ) (x y : QuadraticAlgebra W ϖ 0),
      x ≡ y [SMOD (maximalIdeal (QuadraticAlgebra W ϖ 0) ^ n • ⊤ : Submodule _ (QuadraticAlgebra W ϖ 0))] ↔
        x - y ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, (om_irreducible hϖ).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have keyW : ∀ (n : ℕ) (x y : W),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule W W)] ↔ ϖ ^ n ∣ x - y := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hle : ∀ {m n : ℕ}, m ≤ n → Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} ≤ Ideal.span {ω ^ m} :=
    fun h => (Ideal.span_singleton_le_span_singleton).mpr (pow_dvd_pow _ h)
  refine { toIsHausdorff := inferInstance, prec' := fun f hf => ?_ }
  have hf' : ∀ {m n : ℕ}, m ≤ n → f (2 * m) - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} :=
    fun h => (keyO _ _ _).mp (hf (Nat.mul_le_mul_left 2 h))
  obtain ⟨a, ha⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).re)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).1))
  obtain ⟨b, hb⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).im)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).2))
  refine ⟨⟨a, b⟩, fun n => (keyO _ _ _).mpr ?_⟩
  have h1 : f n - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    (keyO _ _ _).mp (hf (by omega))
  have h2 : f (2 * n) - ⟨a, b⟩ ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    hle (by omega : n ≤ 2 * n) ((mem_span_om_pow n _).mpr
      ⟨by simpa using (keyW _ _ _).mp (ha n), by simpa using (keyW _ _ _).mp (hb n)⟩)
  have e : f n - ⟨a, b⟩ = (f n - f (2 * n)) + (f (2 * n) - ⟨a, b⟩) := by ring
  rw [e]
  exact add_mem h1 h2

end Formalism.BasicNotions.Examples₂.GatR
