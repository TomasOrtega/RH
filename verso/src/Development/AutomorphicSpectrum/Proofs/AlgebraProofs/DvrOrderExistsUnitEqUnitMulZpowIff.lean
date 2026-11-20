import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat

section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Rewrite using `[mul_zpow, ← zpow_mul, mul_pow, ← zpow_natCast (g ^ j), ← zpow_mul, zpow_sub, mul_inv]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
private theorem mul_zpow_mul_inv_pow_mul_zpow_lemma {G : Type*} [CommGroup G] (x y g : G) (k j a : ℤ)
    (M : ℕ) :
    (x * g ^ k) ^ a * ((y * g ^ j) ^ M)⁻¹ = x ^ a * (y ^ M)⁻¹ * g ^ (k * a - j * M) := by
  rw [mul_zpow, ← zpow_mul, mul_pow, ← zpow_natCast (g ^ j), ← zpow_mul, zpow_sub, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Establish `ht0 : algebraMap R K t ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Assume the negation of the conclusion as `he`. Take `⟨n, hn⟩ : ∃ n : ℕ, e = -((n + 1 : ℕ) : ℤ)` from `⟨(-e - 1).toNat, by omega⟩`.

Establish `key : algebraMap R K (r * t ^ (n + 1)) = algebraMap R K v`. Rewrite using `[map_mul, map_pow, hr, hn, zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]`. Establish `hu : IsUnit (r * t ^ (n + 1))`. Rewrite using `[IsFractionRing.injective R K key]`. Conclude with `v.isUnit`.

Rewrite `hu` using `[pow_succ]`. Conclude with `ht.1 (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu))`. Introduce `he lift e to ℕ using he`. Conclude with `⟨v * t ^ e, by rw [map_mul, map_pow, zpow_natCast]⟩`.
-/
theorem dvrOrder_exists_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : R, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ 0 ≤ e := by
  have ht0 : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
  constructor
  · rintro ⟨r, hr⟩
    by_contra he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -((n + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
    have key : algebraMap R K (r * t ^ (n + 1)) = algebraMap R K v := by
      rw [map_mul, map_pow, hr, hn, zpow_neg, zpow_natCast, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]
    have hu : IsUnit (r * t ^ (n + 1)) := by
      rw [IsFractionRing.injective R K key]
      exact v.isUnit
    rw [pow_succ] at hu
    exact ht.1 (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu))
  · intro he
    lift e to ℕ using he
    exact ⟨v * t ^ e, by rw [map_mul, map_pow, zpow_natCast]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Establish `ht0 : algebraMap R K t ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero`. Establish `h1 : 0 ≤ e` using `(GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht v e).1 ⟨r, hr⟩`. Establish `h2 : 0 ≤ -e`.

Use `(GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht r (-e)).1 ⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht0), mul_one]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Conclude with `⟨v, by rw [zpow_zero, mul_one]⟩`.
-/
theorem dvrOrder_exists_unit_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : Rˣ, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ e = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have ht0 : algebraMap R K t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
    have h1 : 0 ≤ e := (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht v e).1 ⟨r, hr⟩
    have h2 : 0 ≤ -e := by
      refine (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht r (-e)).1 ⟨v, ?_⟩
      rw [hr, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht0), mul_one]
    omega
  · rintro rfl
    exact ⟨v, by rw [zpow_zero, mul_one]⟩

end

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ ϖ s hϖ hϖu hs`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hπ0 : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ hinj).2 hπ.ne_zero`. Take `⟨φ, hφ⟩ : ∃ φ : Rˣ →* Kˣ, ∀ x : Rˣ, ((φ x : Kˣ) : K) = algebraMap R K x` from `⟨Units.map (algebraMap R K).toMonoidHom, fun _ => rfl⟩`.

Take `⟨g, hg⟩ : ∃ g : Kˣ, (g : K) = algebraMap R K π` from `⟨Units.mk0 _ hπ0, rfl⟩`. Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ hπ`. Establish `hk : 0 < k`. Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. It suffices to derive a contradiction.

Apply `hϖu` to reduce the goal to its premises. Rewrite using `[hu, h, pow_zero, mul_one]`. Conclude with `u.isUnit`. Conclude with `h`. Establish `hϖK : algebraMap R K ϖ = algebraMap R K u * algebraMap R K π ^ (k : ℤ)`.

Rewrite using `[hu, map_mul, map_pow, zpow_natCast]`. Take `⟨x, y, hy, hxy⟩` from `IsFractionRing.div_surjective (A := R) s`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Apply `hs` to reduce the goal to its premises. Rewrite using `[← hxy, map_zero, zero_div]`. Take `⟨i, w₁, hx⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ`. Take `⟨l, w₂, hy'⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ`. Take `⟨w, hw⟩ : ∃ w : Rˣ, w = w₁ * w₂⁻¹` from `⟨_, rfl⟩`.

Take `⟨j, hj⟩ : ∃ j : ℤ, j = (i : ℤ) - l` from `⟨_, rfl⟩`. Establish `hsK : s = algebraMap R K w * algebraMap R K π ^ j`. Rewrite using `[← hxy, hx, hy', hw, hj]`. Simplify using `only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_sub₀ hπ0, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨k, j, hk, fun M a => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩ : ∃ v : Rˣ, v = u ^ a * (w ^ M)⁻¹` from `⟨_, rfl⟩`. Establish `hU : (φ u * g ^ (k : ℤ)) ^ a * ((φ w * g ^ j) ^ M)⁻¹ = φ v * g ^ ((k : ℤ) * a - j * M)`. Rewrite using `[mul_zpow_mul_inv_pow_mul_zpow_lemma, hv, map_mul, map_zpow, map_inv, map_pow]`. Establish `hU'` using `congrArg (fun z : Kˣ => (z : K)) hU`.

Simplify using `only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hφ, hg] at hU'`. Establish `hX : ∀ r : K, r * s ^ M = algebraMap R K ϖ ^ a ↔ r = algebraMap R K v * algebraMap R K π ^ ((k : ℤ) * a - j * M)`. Introduce `r`. Rewrite using `[← hU', ← hϖK, ← hsK, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hs)]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[exists_congr fun r : R => hX (algebraMap R K r), GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Rewrite using `[exists_congr fun r : Rˣ => hX (algebraMap R K r), GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_unit_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`.
-/
theorem dvr_order_integral_unit_iff : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R) (s : K), ϖ ≠ 0 → ¬ IsUnit ϖ → s ≠ 0 → ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ), ((∃ r : R, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n ≤ a * m) ∧ ((∃ r : Rˣ, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n = a * m) := by
  intro R K _ _ _ _ _ _ ϖ s hϖ hϖu hs
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  obtain ⟨φ, hφ⟩ : ∃ φ : Rˣ →* Kˣ, ∀ x : Rˣ, ((φ x : Kˣ) : K) = algebraMap R K x :=
    ⟨Units.map (algebraMap R K).toMonoidHom, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, (g : K) = algebraMap R K π := ⟨Units.mk0 _ hπ0, rfl⟩
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ hπ
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      apply hϖu
      rw [hu, h, pow_zero, mul_one]
      exact u.isUnit
    · exact h
  have hϖK : algebraMap R K ϖ = algebraMap R K u * algebraMap R K π ^ (k : ℤ) := by
    rw [hu, map_mul, map_pow, zpow_natCast]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hs
    rw [← hxy, map_zero, zero_div]
  obtain ⟨i, w₁, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  obtain ⟨l, w₂, hy'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, w = w₁ * w₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (i : ℤ) - l := ⟨_, rfl⟩
  have hsK : s = algebraMap R K w * algebraMap R K π ^ j := by
    rw [← hxy, hx, hy', hw, hj]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_sub₀ hπ0, zpow_natCast]
    ring
  refine ⟨k, j, hk, fun M a => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, v = u ^ a * (w ^ M)⁻¹ := ⟨_, rfl⟩
  have hU : (φ u * g ^ (k : ℤ)) ^ a * ((φ w * g ^ j) ^ M)⁻¹ =
      φ v * g ^ ((k : ℤ) * a - j * M) := by
    rw [mul_zpow_mul_inv_pow_mul_zpow_lemma, hv, map_mul, map_zpow, map_inv, map_pow]
  have hU' := congrArg (fun z : Kˣ => (z : K)) hU
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, hφ, hg] at hU'
  have hX : ∀ r : K, r * s ^ M = algebraMap R K ϖ ^ a ↔
      r = algebraMap R K v * algebraMap R K π ^ ((k : ℤ) * a - j * M) := by
    intro r
    rw [← hU', ← hϖK, ← hsK, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hs)]
  constructor
  · rw [exists_congr fun r : R => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith
  · rw [exists_congr fun r : Rˣ => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_unit_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith

end GlobalTheory.CompanionTheory.Ar.Flat
