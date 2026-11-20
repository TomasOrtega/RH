import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `hMR hNV Ω _ _ _ U hU ℓ q hℓ hq`. Take `⟨b, σ0, hσ0U, hσ0⟩` from `hMR Ω U hU ℓ hℓ`. Take `⟨D, hDpos, hD⟩` from `hNV Ω U hU q hq`. Take `⟨e, D', hD'ℓ, hDe⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'`. Use `⟨b + e, fun k hk ζ y hζ hy => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩`. Establish `hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a`. Introduce `τ`.

Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])`. Conclude with `⟨i, hi.symm⟩`. Establish `hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a`. Introduce `τ a ha ω hω`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hω`.

Rewrite using `[map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]`. Establish `comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y)`. Introduce `σ hσ τ hτ`. Take `⟨a, ha⟩` from `hpow σ`. Take `⟨c, hc⟩` from `hpow τ`.

Establish `h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]`. Establish `h2` using `hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1`. Rewrite `h2` using `[AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply, AlgEquiv.mul_apply]`. Then use the resulting hypothesis. Establish `hq0 : (q : Ω) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[zero_pow (pow_ne_zero _ hℓ.ne_zero)]`. Conclude with `hq0 hy.symm`. Take `⟨a0, ha0⟩` from `hpow σ0`.

Take `⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a` from `⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one], by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩`. Establish `hjk : ℓ ^ (b + e) ∣ ℓ ^ k` using `pow_dvd_pow ℓ hk`. Establish `hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a`. Introduce `τ hτ`. Establish `hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e))`.

Rewrite using `[← map_pow, hy, map_natCast]`. Take `⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ` from `⟨τ y / y, by field_simp⟩`. Establish `hχj : χ ^ ℓ ^ (b + e) = 1`. Rewrite `hτy` using `[hτy', mul_pow]`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)`.

Establish `hχ1 : χ ^ (ℓ ^ k) = 1`. Take `⟨m, hm⟩` from `hjk`. Rewrite using `[hm, pow_mul, hχj, one_pow]`. Establish `hχ0 : χ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hχ1` using `[zero_pow (pow_ne_zero _ hℓ.ne_zero)]`. Conclude with `zero_ne_one hχ1`. Rewrite using `[map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]`. Conclude with `mul_div_mul_right _ _ (pow_ne_zero _ hχ0)`. Establish `hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1`.

Establish `hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q` using `by rw [← map_pow, hy, map_natCast]`. Rewrite using `[div_pow, hσy, ← pow_mul', pow_mul, hy]`. Establish `hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q`. Rewrite using `[← pow_succ, Nat.sub_add_cancel ha1]`. Rewrite using `[hqa]`.

Clear the denominators using the available nonvanishing facts. Establish `hdiv` using `hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq`. Establish `hb : ℓ ^ b ∣ a - 1`. Rewrite `hdiv` using `[pow_add, hDe]`. Establish `h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e`.

Establish `: (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e` using `by ring`. Rewrite `hdiv` using `[this]`. Then use the resulting hypothesis. Establish `h''` using `Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'`. Conclude with `(Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''`. Take `⟨t, ht⟩` from `hb`.

Establish `hbk : b ≤ k` using `by omega`. Establish `hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b)`. Use `hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero) (pow_dvd_pow ℓ (Nat.sub_le k b))` as an intermediate fact. Rewrite `this` using `[Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk]`. Then use the resulting hypothesis. Apply `hσ0 _ hξ` to reduce the goal to its premises.

Rewrite using `[map_pow, ha, ← pow_mul]`. Establish `h1 : a = 1 + ℓ ^ b * t` using `by rw [← ht]; omega`. Establish `h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t`. Rewrite using `[h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add, Nat.add_sub_cancel' hbk, mul_comm t]`. Rewrite using `[h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.kumMove :
    MoveRoot → NormVal → KumMove := by
  intro hMR hNV Ω _ _ _ U hU ℓ q hℓ hq
  obtain ⟨b, σ0, hσ0U, hσ0⟩ := hMR Ω U hU ℓ hℓ
  obtain ⟨D, hDpos, hD⟩ := hNV Ω U hU q hq
  obtain ⟨e, D', hD'ℓ, hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'
  refine ⟨b + e, fun k hk ζ y hζ hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  have hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a := by
    intro τ a ha ω hω
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hω
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
  have comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y) := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := hpow σ
    obtain ⟨c, hc⟩ := hpow τ
    have h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
        AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]
    have h2 := hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1
    rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply] at h2
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hy
    exact hq0 hy.symm
  obtain ⟨a0, ha0⟩ := hpow σ0
  obtain ⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a :=
    ⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one],
      by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩
  have hjk : ℓ ^ (b + e) ∣ ℓ ^ k := pow_dvd_pow ℓ hk
  have hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a := by
    intro τ hτ
    have hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e)) := by
      rw [← map_pow, hy, map_natCast]
    obtain ⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ := ⟨τ y / y, by field_simp⟩
    have hχj : χ ^ ℓ ^ (b + e) = 1 := by
      rw [hτy', mul_pow] at hτy
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)
    have hχ1 : χ ^ (ℓ ^ k) = 1 := by
      obtain ⟨m, hm⟩ := hjk
      rw [hm, pow_mul, hχj, one_pow]
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hχ1
      exact zero_ne_one hχ1
    rw [map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hχ0)
  have hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1 := by
    have hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q := by rw [← map_pow, hy, map_natCast]
    rw [div_pow, hσy, ← pow_mul', pow_mul, hy]
    have hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel ha1]
    rw [hqa]
    field_simp
  have hdiv := hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq
  have hb : ℓ ^ b ∣ a - 1 := by
    rw [pow_add, hDe] at hdiv
    have h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e := by
      have : (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e := by ring
      rwa [this] at hdiv
    have h'' := Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'
    exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''
  obtain ⟨t, ht⟩ := hb
  have hbk : b ≤ k := by omega
  have hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b) := by
    have := hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero)
      (pow_dvd_pow ℓ (Nat.sub_le k b))
    rwa [Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk] at this
  apply hσ0 _ hξ
  rw [map_pow, ha, ← pow_mul]
  have h1 : a = 1 + ℓ ^ b * t := by rw [← ht]; omega
  have h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t := by
    rw [h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hbk, mul_comm t]
  rw [h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
