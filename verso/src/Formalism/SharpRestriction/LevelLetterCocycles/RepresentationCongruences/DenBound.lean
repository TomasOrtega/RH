import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨u, hu⟩` from `l_eq_unit_mul_pow hϖ P.hl0`. Use `set e := eO (O := O) l with he`. Establish `hdiv : ∀ k : ℕ, ϖ ^ (e * k) ∣ x → (l : O) ^ k ∣ x`. Introduce and unpack `k ⟨z, hz⟩`.

Use `⟨((↑(u⁻¹) : O)) ^ k * z, ?_⟩` and prove the remaining obligations. Establish `hone : (↑u : O) ^ k * (↑(u⁻¹) : O) ^ k = 1` using `by rw [← mul_pow, Units.mul_inv, one_pow]`. Rewrite using `[hz, hu, mul_pow, ← pow_mul]`. Take the linear combination `(-(ϖ ^ (e * k) * z)) * hone`. Use `set de := ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊ with hde`.

Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality. Conclude with `⟨dvd_zero _, fun _ => dvd_zero _⟩`. Take `⟨v, ε, hxe⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`. Distinguish the cases in `hv : e * κ ≤ v`.

Take `⟨t, ht⟩` from `Nat.exists_eq_add_of_le hv`. Establish `h1 : (l : O) ^ κ ∣ x` using `hdiv κ ⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩`. Conclude with `⟨(pow_dvd_pow _ (Nat.sub_le _ _)).trans h1, fun _ => h1⟩`. Use `push_neg at hv`. Use `set k := e * κ - v with hk`.

Establish `hdist` using `(ContPA.dist_X_pow (O := O) B).1`. Establish `hmem : P.p 1 ^ y ∈ Ideal.span {C ϖ ^ k, (X : O⟦X⟧) ^ B}`. Establish `hvk : v + k = e * κ` using `by omega`. Establish `hlO : (l : O) ^ κ = ϖ ^ v * (ϖ ^ k * (↑u : O) ^ κ)`. Rewrite using `[hu, mul_pow, ← pow_mul, ← hvk, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlk : (C (l : O) : O⟦X⟧) ^ κ = C ϖ ^ v * (C ϖ ^ k * C ((↑u : O) ^ κ))`. Rewrite using `[← map_pow, hlO, map_mul, map_mul, map_pow, map_pow]`. Establish `hc : C ϖ ^ v * (P.p 1 ^ y * C (↑ε : O) - C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁)) = (-U₂) * (X : O⟦X⟧) ^ B`. Establish `hxC : (C x : O⟦X⟧) = C (↑ε : O) * C ϖ ^ v` using `by rw [hxe, map_mul, map_pow]`.

Rewrite `h` using `[hxC, hlk]`. Take the linear combination `h`. Take `⟨z, hz⟩` from `ContM_cancel_unif hϖ hdist v hc`. Establish `hε : P.p 1 ^ y = C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁ * C (↑(ε⁻¹) : O)) + (X : O⟦X⟧) ^ B * (z * C (↑(ε⁻¹) : O))`. Establish `hεε : (C (↑ε : O) : O⟦X⟧) * C (↑(ε⁻¹) : O) = 1`.

Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Take the linear combination `(-(P.p 1 ^ y)) * hεε + C (↑(ε⁻¹) : O) * hz`. Rewrite using `[hε]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))`. Establish `hkc` using `(mem_iff_le_cont hϖ hdist _ k).1 hmem`.

Prove the components needed by the constructor for the conclusion. Take `⟨hne, hle⟩` from `P.constant_le_rpow_of_three_le hϖ B y hB hy`. Establish `hkc' : k ≤ (cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat`. Rewrite `hkc` using `[← ENat.coe_toNat hne]`. Conclude with `hkc` after adjusting the coercions.

Establish `hr : max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) ≤ (de : ℝ)` using `Nat.le_ceil _`. Establish `he0 : (0 : ℝ) ≤ e` using `Nat.cast_nonneg _`. Establish `hkr : (k : ℝ) ≤ (e : ℝ) * de`. Use `mul_le_mul_of_nonneg_left hr he0` as an intermediate fact. Establish `hk' : (k : ℝ) ≤ ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ)` using `by exact_mod_cast hkc'`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkn : k ≤ e * de` using `by exact_mod_cast hkr`. Apply `hdiv` to reduce the goal to its premises. Establish `hle2 : e * (κ - de) ≤ v` using `by rw [Nat.mul_sub]; omega`. Take `⟨t, ht⟩` from `Nat.exists_eq_add_of_le hle2`.

Conclude with `⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩`. Introduce `hlt`. Establish `h0` using `P.cont_X_pow_pow_eq_zero_of_gt hϖ B y hB hy hlt`. Rewrite `hkc` using `[h0]`. Establish `: k = 0` using `by exact_mod_cast nonpos_iff_eq_zero.mp hkc`.

Use linear arithmetic over natural numbers and integers.
-/
theorem den_bound {l : ℕ} [Fact l.Prime] (P : PhiData O l) (y B κ : ℕ) (hy : 1 ≤ y) (hB : 1 ≤ B)
    (x : O) (U₁ U₂ : O⟦X⟧)
    (h : P.p 1 ^ y * C x = C (l : O) ^ κ * 1 * U₁ - X ^ B * U₂) :
    (l : O) ^ (κ - ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊) ∣ x ∧
      (l * y < B → (l : O) ^ κ ∣ x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  set e := eO (O := O) l with he
  have hdiv : ∀ k : ℕ, ϖ ^ (e * k) ∣ x → (l : O) ^ k ∣ x := by
    rintro k ⟨z, hz⟩
    refine ⟨((↑(u⁻¹) : O)) ^ k * z, ?_⟩
    have hone : (↑u : O) ^ k * (↑(u⁻¹) : O) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
    rw [hz, hu, mul_pow, ← pow_mul]
    linear_combination (-(ϖ ^ (e * k) * z)) * hone
  set de := ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊ with hde
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨dvd_zero _, fun _ => dvd_zero _⟩
  obtain ⟨v, ε, hxe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  by_cases hv : e * κ ≤ v
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hv
    have h1 : (l : O) ^ κ ∣ x := hdiv κ ⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩
    exact ⟨(pow_dvd_pow _ (Nat.sub_le _ _)).trans h1, fun _ => h1⟩
  push_neg at hv
  set k := e * κ - v with hk
  have hdist := (ContPA.dist_X_pow (O := O) B).1

  have hmem : P.p 1 ^ y ∈ Ideal.span {C ϖ ^ k, (X : O⟦X⟧) ^ B} := by
    have hvk : v + k = e * κ := by omega
    have hlO : (l : O) ^ κ = ϖ ^ v * (ϖ ^ k * (↑u : O) ^ κ) := by
      rw [hu, mul_pow, ← pow_mul, ← hvk, pow_add]; ring
    have hlk : (C (l : O) : O⟦X⟧) ^ κ = C ϖ ^ v * (C ϖ ^ k * C ((↑u : O) ^ κ)) := by
      rw [← map_pow, hlO, map_mul, map_mul, map_pow, map_pow]
    have hc : C ϖ ^ v * (P.p 1 ^ y * C (↑ε : O) - C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁)) =
        (-U₂) * (X : O⟦X⟧) ^ B := by
      have hxC : (C x : O⟦X⟧) = C (↑ε : O) * C ϖ ^ v := by rw [hxe, map_mul, map_pow]
      rw [hxC, hlk] at h
      linear_combination h
    obtain ⟨z, hz⟩ := ContM_cancel_unif hϖ hdist v hc
    have hε : P.p 1 ^ y = C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁ * C (↑(ε⁻¹) : O)) +
        (X : O⟦X⟧) ^ B * (z * C (↑(ε⁻¹) : O)) := by
      have hεε : (C (↑ε : O) : O⟦X⟧) * C (↑(ε⁻¹) : O) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      linear_combination (-(P.p 1 ^ y)) * hεε + C (↑(ε⁻¹) : O) * hz
    rw [hε]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have hkc := (mem_iff_le_cont hϖ hdist _ k).1 hmem
  constructor
  · obtain ⟨hne, hle⟩ := P.constant_le_rpow_of_three_le hϖ B y hB hy
    have hkc' : k ≤ (cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat := by
      rw [← ENat.coe_toNat hne] at hkc
      exact_mod_cast hkc
    have hr : max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) ≤ (de : ℝ) := Nat.le_ceil _
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hkr : (k : ℝ) ≤ (e : ℝ) * de := by
      have := mul_le_mul_of_nonneg_left hr he0
      have hk' : (k : ℝ) ≤ ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ) := by exact_mod_cast hkc'
      linarith
    have hkn : k ≤ e * de := by exact_mod_cast hkr
    apply hdiv
    have hle2 : e * (κ - de) ≤ v := by rw [Nat.mul_sub]; omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle2
    exact ⟨↑ε * ϖ ^ t, by rw [hxe, ht, pow_add]; ring⟩
  · intro hlt
    have h0 := P.cont_X_pow_pow_eq_zero_of_gt hϖ B y hB hy hlt
    rw [h0] at hkc
    have : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hkc
    omega

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
