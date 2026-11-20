import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.SW.QuadField

section Val

variable {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))

/- English proof (translation)
Establish `h0 : w x ≠ 0` using `(Valuation.ne_zero_iff w).2 hx`. Take `⟨a, ha⟩ : ∃ a : ℤ, w x = WithZero.exp a` from `⟨WithZero.log (w x), (WithZero.exp_log h0).symm⟩`. Rewrite `h1` using `[ha]`. Establish `ha0 : a ≤ 0`. Rewrite `h1` using `[← WithZero.exp_zero, WithZero.exp_le_exp]`.

Conclude with `h1`. Use `⟨(-a).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, Int.toNat_of_nonneg (by omega), neg_neg]`.
-/
theorem exists_exp {x : K} (hx : x ≠ 0) (h1 : w x ≤ 1) :
    ∃ k : ℕ, w x = WithZero.exp (-(k : ℤ)) := by
  have h0 : w x ≠ 0 := (Valuation.ne_zero_iff w).2 hx
  obtain ⟨a, ha⟩ : ∃ a : ℤ, w x = WithZero.exp a := ⟨WithZero.log (w x), (WithZero.exp_log h0).symm⟩
  rw [ha] at h1
  have ha0 : a ≤ 0 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  refine ⟨(-a).toNat, ?_⟩
  rw [ha, Int.toNat_of_nonneg (by omega), neg_neg]

/- English proof (translation)
Rewrite using `[map_pow, hϖ, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem val_pow {ϖ : K} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    w (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]
  congr 1
  simp

variable {D : K}

/- English proof (translation)
Introduce `hN`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Establish `hx : x ≠ 0` using `h.resolve_right (by simp)`. Conclude with `hx (by simpa using hN)`. Establish `he : (x / y) ^ 2 = D`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hN`. Distinguish the cases in `hle : w (x / y) ≤ 1`. Apply `hsq _ hle` to reduce the goal to its premises. Rewrite using `[he, sub_self, map_zero]`.

Conclude with `zero_lt_one`. Use `push_neg at hle`. Establish `h2 : w (x / y) ^ 2 = 1` using `by rw [← map_pow, he, hD]`. Establish `h3 : (1 : WithZero (Multiplicative ℤ)) < w (x / y) ^ 2` using `one_lt_pow' hle two_ne_zero`. Rewrite `h3` using `[h2]`.

Conclude with `lt_irrefl _ h3`.
-/
theorem norm_ne_zero (hD : w D = 1) (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) {x y : K}
    (h : x ≠ 0 ∨ y ≠ 0) : x ^ 2 - D * y ^ 2 ≠ 0 := by
  intro hN
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := h.resolve_right (by simp)
    exact hx (by simpa using hN)
  · have he : (x / y) ^ 2 = D := by
      field_simp
      linear_combination hN
    by_cases hle : w (x / y) ≤ 1
    · apply hsq _ hle
      rw [he, sub_self, map_zero]
      exact zero_lt_one
    · push_neg at hle
      have h2 : w (x / y) ^ 2 = 1 := by rw [← map_pow, he, hD]
      have h3 : (1 : WithZero (Multiplicative ℤ)) < w (x / y) ^ 2 := one_lt_pow' hle two_ne_zero
      rw [h2] at h3
      exact lt_irrefl _ h3

/- English proof (translation)
Break down `lt_or_eq_of_le hq with hq1 | hq1` into its components or cases. Establish `hp1 : w p = 1` using `h.resolve_right (ne_of_lt hq1)`. Establish `hA : w (p ^ 2) = 1` using `by rw [map_pow, hp1, one_pow]`. Establish `hB : w (D * q ^ 2) < 1`. Rewrite using `[map_mul, map_pow, hD, one_mul]`.

Conclude with `pow_lt_one₀ zero_le' hq1 two_ne_zero`. Rewrite using `[sub_eq_add_neg, Valuation.map_add_eq_of_lt_left w (by rwa [Valuation.map_neg, hA]), hA]`. Establish `hq0 : q ≠ 0`. Introduce `h0`. Rewrite `hq1` using `[h0, map_zero]`.

Conclude with `zero_ne_one hq1`. Establish `hsplit : p ^ 2 - D * q ^ 2 = q ^ 2 * ((p / q) ^ 2 - D)`. Clear the denominators using the available nonvanishing facts. Establish `he : w (p / q) ≤ 1` using `by rw [map_div₀, hq1, div_one]; exact hp`. Establish `hle : w ((p / q) ^ 2 - D) ≤ 1`.

Use `le_trans (Valuation.map_sub w _ _) (max_le ?_ (le_of_eq hD))` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_le_one₀ zero_le' he`. Establish `hge : ¬ w ((p / q) ^ 2 - D) < 1` using `hsq _ he`. Rewrite using `[hsplit, map_mul, map_pow, hq1, one_pow, one_mul]`.

Conclude with `le_antisymm hle (not_lt.1 hge)`.
-/
theorem norm_val (hD : w D = 1) (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) {p q : K}
    (hp : w p ≤ 1) (hq : w q ≤ 1) (h : w p = 1 ∨ w q = 1) : w (p ^ 2 - D * q ^ 2) = 1 := by
  rcases lt_or_eq_of_le hq with hq1 | hq1
  · have hp1 : w p = 1 := h.resolve_right (ne_of_lt hq1)
    have hA : w (p ^ 2) = 1 := by rw [map_pow, hp1, one_pow]
    have hB : w (D * q ^ 2) < 1 := by
      rw [map_mul, map_pow, hD, one_mul]
      exact pow_lt_one₀ zero_le' hq1 two_ne_zero
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left w (by rwa [Valuation.map_neg, hA]), hA]
  · have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq1
      exact zero_ne_one hq1
    have hsplit : p ^ 2 - D * q ^ 2 = q ^ 2 * ((p / q) ^ 2 - D) := by
      field_simp
    have he : w (p / q) ≤ 1 := by rw [map_div₀, hq1, div_one]; exact hp
    have hle : w ((p / q) ^ 2 - D) ≤ 1 := by
      refine le_trans (Valuation.map_sub w _ _) (max_le ?_ (le_of_eq hD))
      rw [map_pow]
      exact pow_le_one₀ zero_le' he
    have hge : ¬ w ((p / q) ^ 2 - D) < 1 := hsq _ he
    rw [hsplit, map_mul, map_pow, hq1, one_pow, one_mul]
    exact le_antisymm hle (not_lt.1 hge)

end Val

section Quad

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
  (w : Valuation K (WithZero (Multiplicative ℤ))) (B : Module.Basis (Fin 2) K A) {D : K}

/- English proof (translation)
Establish `hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1`. Rewrite using `[← map_mul, mul_one_div_cancel hN, map_one]`. Rewrite using `[← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]`. Simplify using `only [map_mul, map_sub, map_neg, map_pow, ← hBD]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_conj_div (hBD : B 1 * B 1 = algebraMap K A D) (p q : K)
    (hN : p ^ 2 - D * q ^ 2 ≠ 0) :
    (algebraMap K A p + algebraMap K A q * B 1) *
      (algebraMap K A (p / (p ^ 2 - D * q ^ 2)) +
        algebraMap K A (-q / (p ^ 2 - D * q ^ 2)) * B 1) = 1 := by
  have hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1 := by
    rw [← map_mul, mul_one_div_cancel hN, map_one]
  rw [← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]
  simp only [map_mul, map_sub, map_neg, map_pow, ← hBD]
  ring

/- English proof (translation)
Use `⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `B.ne_zero 0`. Rewrite `h1` using `[hB0]`. Conclude with `h1 h.symm`.

Introduce `x hx`. Establish `hxpq : x = algebraMap K A (B.repr x 0) + algebraMap K A (B.repr x 1) * B 1` using `by conv_lhs => rw [← B.sum_repr x]`. Rewrite using `[Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `hpq : B.repr x 0 ≠ 0 ∨ B.repr x 1 ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hxpq, hc.1, hc.2]`. Simplify using the standard rewrite rules. Take `⟨p, q, hxe, hpq'⟩ : ∃ p q : K, x = algebraMap K A p + algebraMap K A q * B 1 ∧ (p ≠ 0 ∨ q ≠ 0)` from `⟨_, _, hxpq, hpq⟩`.

Establish `hN` using `hne p q hpq'`. Use `⟨algebraMap K A (p / (p ^ 2 - D * q ^ 2)) + algebraMap K A (-q / (p ^ 2 - D * q ^ 2)) * B 1, ?_⟩` and prove the remaining obligations. Establish `hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1`. Rewrite using `[← map_mul, mul_one_div_cancel hN, map_one]`. Rewrite using `[hxe, ← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]`.

Simplify using `only [map_mul, map_sub, map_neg, map_pow, ← hBD]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isField (hB0 : B 0 = 1) (hBD : B 1 * B 1 = algebraMap K A D)
    (hne : ∀ p q : K, p ≠ 0 ∨ q ≠ 0 → p ^ 2 - D * q ^ 2 ≠ 0) : IsField A := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    have h1 := B.ne_zero 0
    rw [hB0] at h1
    exact h1 h.symm
  · intro x hx
    have hxpq : x = algebraMap K A (B.repr x 0) + algebraMap K A (B.repr x 1) * B 1 := by
      conv_lhs => rw [← B.sum_repr x]
      rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
    have hpq : B.repr x 0 ≠ 0 ∨ B.repr x 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      rw [hxpq, hc.1, hc.2]
      simp
    obtain ⟨p, q, hxe, hpq'⟩ : ∃ p q : K,
        x = algebraMap K A p + algebraMap K A q * B 1 ∧ (p ≠ 0 ∨ q ≠ 0) := ⟨_, _, hxpq, hpq⟩
    have hN := hne p q hpq'
    refine ⟨algebraMap K A (p / (p ^ 2 - D * q ^ 2)) + algebraMap K A (-q / (p ^ 2 - D * q ^ 2)) * B 1, ?_⟩
    have hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1 := by
      rw [← map_mul, mul_one_div_cancel hN, map_one]
    rw [hxe, ← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]
    simp only [map_mul, map_sub, map_neg, map_pow, ← hBD]
    ring

variable {ϖ : K}

/- English proof (translation)
Establish `hrep : ∀ a b : K, B.repr (algebraMap K A a + algebraMap K A b * B 1) 0 = a ∧ B.repr (algebraMap K A a + algebraMap K A b * B 1) 1 = b`. Introduce `a b`. Establish `h : algebraMap K A a + algebraMap K A b * B 1 = a • B 0 + b • B 1`. Rewrite using `[hB0, Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[h]`.

Simplify using `[Finsupp.single_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨p, q, hxpq, hp, hq⟩ : ∃ p q : K, x = algebraMap K A p + algebraMap K A q * B 1 ∧ w p ≤ 1 ∧ w q ≤ 1 := by`. Use `⟨B.repr x 0, B.repr x 1, ?_, hx 0, hx 1⟩` and prove the remaining obligations. Use `conv_lhs => rw [← B.sum_repr x]`. Rewrite using `[Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]`.

Substitute `hxpq` using the available equality. Establish `hpq : p ≠ 0 ∨ q ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hx0` to reduce the goal to its premises.

Rewrite using `[hc.1, hc.2]`. Simplify using the standard rewrite rules. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ` using `[h0, map_zero]`.

Conclude with `WithZero.zero_ne_coe hϖ`. Choose the witnesses or unpack the hypotheses as in `⟨m, hpm, hqm, hor⟩ : ∃ m : ℕ, w p ≤ WithZero.exp (-(m : ℤ)) ∧ w q ≤ WithZero.exp (-(m : ℤ)) ∧ (w p = WithZero.exp (-(m : ℤ)) ∨ w q = WithZero.exp (-(m : ℤ))) := by`. Distinguish the cases in `hp0 : p = 0`. Take `⟨b, hb⟩` from `exists_exp w (hpq.resolve_left (not_not.2 hp0)) hq`. Conclude with `⟨b, (by rw [hp0, map_zero]; exact zero_le'), le_of_eq hb, Or.inr hb⟩`.

Distinguish the cases in `hq0 : q = 0`. Take `⟨a, ha⟩` from `exists_exp w hp0 hp`. Conclude with `⟨a, le_of_eq ha, (by rw [hq0, map_zero]; exact zero_le'), Or.inl ha⟩`. Take `⟨a, ha⟩` from `exists_exp w hp0 hp`. Take `⟨b, hb⟩` from `exists_exp w hq0 hq`.

Break down `le_total a b with hab | hab` into its components or cases. Use `⟨a, le_of_eq ha, ?_, Or.inl ha⟩` and prove the remaining obligations. Rewrite using `[hb, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Use `⟨b, ?_, le_of_eq hb, Or.inr hb⟩` and prove the remaining obligations.

Rewrite using `[ha, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hc : w ((ϖ ^ m)⁻¹) = WithZero.exp (m : ℤ)`. Rewrite using `[map_inv₀, val_pow w hϖ m, ← WithZero.exp_neg, neg_neg]`. Establish `hone : WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ) = 1`.

Rewrite using `[← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]`. Establish `hp' : w (p * (ϖ ^ m)⁻¹) ≤ 1`. Rewrite using `[map_mul, hc, ← hone]`. Conclude with `mul_le_mul' hpm le_rfl`. Establish `hq' : w (q * (ϖ ^ m)⁻¹) ≤ 1`.

Rewrite using `[map_mul, hc, ← hone]`. Conclude with `mul_le_mul' hqm le_rfl`. Establish `hor' : w (p * (ϖ ^ m)⁻¹) = 1 ∨ w (q * (ϖ ^ m)⁻¹) = 1`. Break down `hor with h | h` into its components or cases. Use `left`.

Rewrite using `[map_mul, hc, h, hone]`. Use `right`. Rewrite using `[map_mul, hc, h, hone]`. Establish `hN1` using `norm_val w hD hsq hp' hq' hor'`. Establish `hN : (p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2 ≠ 0`.

Introduce `h`. Rewrite `hN1` using `[h, map_zero]`. Conclude with `zero_ne_one hN1`. Use `⟨m, algebraMap K A (p * (ϖ ^ m)⁻¹) + algebraMap K A (q * (ϖ ^ m)⁻¹) * B 1, algebraMap K A (p * (ϖ ^ m)⁻¹ / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) + algebraMap K A (-(q * (ϖ ^ m)⁻¹) / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) * B 1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j fin_cases j`.

Rewrite using `[show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1]`. Conclude with `hp'`. Rewrite using `[show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2]`. Conclude with `hq'`. Introduce `j fin_cases j`.

Rewrite using `[show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1, map_div₀, hN1, div_one]`. Conclude with `hp'`. Rewrite using `[show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2, map_div₀, hN1, div_one, Valuation.map_neg]`. Conclude with `hq'`. Conclude with `mul_conj_div B hBD _ _ hN`.

Establish `e1 : ϖ ^ m * (p * (ϖ ^ m)⁻¹) = p` using `by field_simp`. Establish `e2 : ϖ ^ m * (q * (ϖ ^ m)⁻¹) = q` using `by field_simp`. Rewrite using `[mul_add, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, e1, e2]`.
-/
theorem exists_factor (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hB0 : B 0 = 1)
    (hBD : B 1 * B 1 = algebraMap K A D) (hD : w D = 1)
    (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) (x : A) (hx : ∀ j, w (B.repr x j) ≤ 1)
    (hx0 : x ≠ 0) :
    ∃ (i : ℕ) (u u' : A), (∀ j, w (B.repr u j) ≤ 1) ∧ (∀ j, w (B.repr u' j) ≤ 1) ∧ u * u' = 1 ∧
      x = (algebraMap K A ϖ) ^ i * u := by
  have hrep : ∀ a b : K, B.repr (algebraMap K A a + algebraMap K A b * B 1) 0 = a ∧
      B.repr (algebraMap K A a + algebraMap K A b * B 1) 1 = b := by
    intro a b
    have h : algebraMap K A a + algebraMap K A b * B 1 = a • B 0 + b • B 1 := by
      rw [hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [h]
    simp [Finsupp.single_apply]
  obtain ⟨p, q, hxpq, hp, hq⟩ : ∃ p q : K, x = algebraMap K A p + algebraMap K A q * B 1 ∧
      w p ≤ 1 ∧ w q ≤ 1 := by
    refine ⟨B.repr x 0, B.repr x 1, ?_, hx 0, hx 1⟩
    conv_lhs => rw [← B.sum_repr x]
    rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
  subst hxpq
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx0
    rw [hc.1, hc.2]
    simp
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨m, hpm, hqm, hor⟩ : ∃ m : ℕ, w p ≤ WithZero.exp (-(m : ℤ)) ∧ w q ≤ WithZero.exp (-(m : ℤ)) ∧
      (w p = WithZero.exp (-(m : ℤ)) ∨ w q = WithZero.exp (-(m : ℤ))) := by
    by_cases hp0 : p = 0
    · obtain ⟨b, hb⟩ := exists_exp w (hpq.resolve_left (not_not.2 hp0)) hq
      exact ⟨b, (by rw [hp0, map_zero]; exact zero_le'), le_of_eq hb, Or.inr hb⟩
    by_cases hq0 : q = 0
    · obtain ⟨a, ha⟩ := exists_exp w hp0 hp
      exact ⟨a, le_of_eq ha, (by rw [hq0, map_zero]; exact zero_le'), Or.inl ha⟩
    obtain ⟨a, ha⟩ := exists_exp w hp0 hp
    obtain ⟨b, hb⟩ := exists_exp w hq0 hq
    rcases le_total a b with hab | hab
    · refine ⟨a, le_of_eq ha, ?_, Or.inl ha⟩
      rw [hb, WithZero.exp_le_exp]
      omega
    · refine ⟨b, ?_, le_of_eq hb, Or.inr hb⟩
      rw [ha, WithZero.exp_le_exp]
      omega
  have hc : w ((ϖ ^ m)⁻¹) = WithZero.exp (m : ℤ) := by
    rw [map_inv₀, val_pow w hϖ m, ← WithZero.exp_neg, neg_neg]
  have hone : WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ) = 1 := by
    rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hp' : w (p * (ϖ ^ m)⁻¹) ≤ 1 := by
    rw [map_mul, hc, ← hone]
    exact mul_le_mul' hpm le_rfl
  have hq' : w (q * (ϖ ^ m)⁻¹) ≤ 1 := by
    rw [map_mul, hc, ← hone]
    exact mul_le_mul' hqm le_rfl
  have hor' : w (p * (ϖ ^ m)⁻¹) = 1 ∨ w (q * (ϖ ^ m)⁻¹) = 1 := by
    rcases hor with h | h
    · left
      rw [map_mul, hc, h, hone]
    · right
      rw [map_mul, hc, h, hone]
  have hN1 := norm_val w hD hsq hp' hq' hor'
  have hN : (p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨m, algebraMap K A (p * (ϖ ^ m)⁻¹) + algebraMap K A (q * (ϖ ^ m)⁻¹) * B 1,
    algebraMap K A (p * (ϖ ^ m)⁻¹ / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) +
      algebraMap K A (-(q * (ϖ ^ m)⁻¹) / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) * B 1,
    ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1]
      exact hp'
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2]
      exact hq'
  · intro j
    fin_cases j
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1, map_div₀, hN1, div_one]
      exact hp'
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2, map_div₀, hN1, div_one,
        Valuation.map_neg]
      exact hq'
  · exact mul_conj_div B hBD _ _ hN
  · have e1 : ϖ ^ m * (p * (ϖ ^ m)⁻¹) = p := by field_simp
    have e2 : ϖ ^ m * (q * (ϖ ^ m)⁻¹) = q := by field_simp
    rw [mul_add, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, e1, e2]

/- English proof (translation)
Assume the negation of the conclusion as `hji`. Use `push_neg at hji`. Take `⟨k, rfl⟩ : ∃ k, j = i + (k + 1)` from `⟨j - i - 1, by omega⟩`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`.

Rewrite `hϖ` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`. Establish `hi : IsUnit ((algebraMap K A ϖ) ^ i)` using `(IsUnit.map (algebraMap K A) (Ne.isUnit hϖ0)).pow i`. Establish `h1 : (1 : A) = algebraMap K A (ϖ ^ (k + 1)) * u`. Apply `hi.mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[mul_one, map_pow, ← mul_assoc, ← pow_add]`. Conclude with `h`. Establish `hu' : u = algebraMap K A ((ϖ ^ (k + 1))⁻¹)`. Establish `hk : algebraMap K A ((ϖ ^ (k + 1))⁻¹) * algebraMap K A (ϖ ^ (k + 1)) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, hk, one_mul]`. Use `_ = algebraMap K A ((ϖ ^ (k + 1))⁻¹) := by rw [← h1, mul_one]`. Establish `hr : B.repr u 0 = (ϖ ^ (k + 1))⁻¹`. Rewrite using `[hu', Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, B.repr_self]`.

Simplify using the standard rewrite rules. Establish `h2` using `hu 0`. Rewrite `h2` using `[hr, map_inv₀, map_pow, hϖ, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_eq_mul (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hB0 : B 0 = 1) {i j : ℕ} {u : A}
    (hu : ∀ l, w (B.repr u l) ≤ 1)
    (h : (algebraMap K A ϖ) ^ i = (algebraMap K A ϖ) ^ j * u) : j ≤ i := by
  by_contra hji
  push_neg at hji
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hi : IsUnit ((algebraMap K A ϖ) ^ i) := (IsUnit.map (algebraMap K A) (Ne.isUnit hϖ0)).pow i
  have h1 : (1 : A) = algebraMap K A (ϖ ^ (k + 1)) * u := by
    apply hi.mul_left_cancel
    rw [mul_one, map_pow, ← mul_assoc, ← pow_add]
    exact h
  have hu' : u = algebraMap K A ((ϖ ^ (k + 1))⁻¹) := by
    have hk : algebraMap K A ((ϖ ^ (k + 1))⁻¹) * algebraMap K A (ϖ ^ (k + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), map_one]
    calc u = algebraMap K A ((ϖ ^ (k + 1))⁻¹) * (algebraMap K A (ϖ ^ (k + 1)) * u) := by
          rw [← mul_assoc, hk, one_mul]
      _ = algebraMap K A ((ϖ ^ (k + 1))⁻¹) := by rw [← h1, mul_one]
  have hr : B.repr u 0 = (ϖ ^ (k + 1))⁻¹ := by
    rw [hu', Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, B.repr_self]
    simp
  have h2 := hu 0
  rw [hr, map_inv₀, map_pow, hϖ, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h2
  simp at h2
  omega

end Quad

section Place

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Use `⟨(π : v.adicCompletion F), hv, ?_⟩` and prove the remaining obligations. Establish `h0 : WithZero.exp (-1 : ℤ) ≠ 0` using `WithZero.exp_ne_zero`.

Rewrite using `[NumberField.FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Establish `he : Multiplicative.toAdd (WithZero.unzero h0) = -1` using `rfl`. Rewrite using `[he, zpow_neg_one, NNReal.coe_inv]`. Simplify using the standard rewrite rules.
-/
theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, Valued.v ϖ = WithZero.exp (-1 : ℤ) ∧
      ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  refine ⟨(π : v.adicCompletion F), hv, ?_⟩
  have h0 : WithZero.exp (-1 : ℤ) ≠ 0 := WithZero.exp_ne_zero
  rw [NumberField.FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ h0]
  have he : Multiplicative.toAdd (WithZero.unzero h0) = -1 := rfl
  rw [he, zpow_neg_one, NNReal.coe_inv]
  simp

end Place

/- English proof (translation)
Rewrite using `[← B.sum_repr y]`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy k) (hB k j)`.
-/
private theorem basis_repr_mem_subring_of_change_of_basis {K V ι ι' : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (S : Subring K) (B : Module.Basis ι K V) (B' : Module.Basis ι' K V)
    (hB : ∀ k j, B'.repr (B k) j ∈ S) (y : V) (hy : ∀ k, B.repr y k ∈ S) (j : ι') :
    B'.repr y j ∈ S := by
  rw [← B.sum_repr y]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy k) (hB k j)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ d b b₂ D hb0 _ hbD v hD _ H1 H2 hno`. Establish `hB0 : Algebra.TensorProduct.basis (Fv F v) b₂ 0 = 1`. Rewrite using `[Algebra.TensorProduct.basis_apply, hb0]`. Both sides reduce to the same expression. Establish `hBD : Algebra.TensorProduct.basis (Fv F v) b₂ 1 * Algebra.TensorProduct.basis (Fv F v) b₂ 1 = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) D)`.

Rewrite using `[Algebra.TensorProduct.basis_apply, ← Algebra.TensorProduct.includeRight_apply (R := F) (A := Fv F v), ← map_mul, hbD, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`. Establish `hsq : ∀ e : Fv F v, Valued.v e ≤ 1 → ¬ Valued.v (e ^ 2 - algebraMap F (Fv F v) D) < 1` using `fun e he hlt => hno ⟨⟨e, he⟩, hlt⟩`. Establish `hfield : IsField (Fv F v ⊗[F] E)` using `isField (Algebra.TensorProduct.basis (Fv F v) b₂) hB0 hBD (fun p q h => norm_ne_zero Valued.v hD hsq h)`. Use `haveI := hfield.nontrivial`. Take `⟨ϖ, hϖ, hnorm⟩` from `exists_unif v`.

Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`. Establish `hϖO : ϖ ∈ v.adicCompletionIntegers F` using `by show Valued.v ϖ ≤ 1`.

Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Establish `hincl2 : ∀ j, Algebra.TensorProduct.basis (Fv F v) b₂ j = inclR (Fv F v) (b₂ j)`. Introduce `j`. Rewrite using `[Algebra.TensorProduct.basis_apply]`.

Both sides reduce to the same expression. Establish `hincl : ∀ k, Algebra.TensorProduct.basis (Fv F v) b k = inclR (Fv F v) (b k)`. Introduce `k`. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression.

Establish `T1 : ∀ y : Fv F v ⊗[F] E, (∀ j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F) → y ∈ intK b v`. Introduce `y hy`. Simplify using `only [intK, Set.mem_setOf_eq]`. Introduce `k`. Conclude with `basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b₂) (Algebra.TensorProduct.basis (Fv F v) b) (fun j k => by rw [hincl2]; exact H2 j k) y hy k`.

Establish `T2 : ∀ y ∈ intK b v, ∀ j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F`. Introduce `y hy j`. Simplify using `only [intK, Set.mem_setOf_eq] at hy`. Conclude with `basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b) (Algebra.TensorProduct.basis (Fv F v) b₂) (fun k j => by rw [hincl]; exact H1 k j) y hy j`. Establish `hsig : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ`.

Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`. Use `⟨hfield, fun i => (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `⟨(IsUnit.map _ (Ne.isUnit hϖ0)).pow i, T1 _ fun j => ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← map_pow, Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]`. Use `(v.adicCompletionIntegers F).mul_mem _ _ ((v.adicCompletionIntegers F).pow_mem hϖO i) ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `(v.adicCompletionIntegers F).one_mem`.

Conclude with `(v.adicCompletionIntegers F).zero_mem`. Introduce `i`. Use `⟨ϖ ^ (2 * i), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow (algebraMap (Fv F v) (Fv F v ⊗[F] E)), map_pow (sigR (Fv F v) σ), hsig, ← pow_add, two_mul]`. Rewrite using `[norm_pow, hnorm, inv_pow]`.

Simplify using `[qv]`. Introduce `x hx hux`. Take `⟨i, u, u', hu, hu', huu, hxu⟩` from `exists_factor Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 hBD hD hsq x (fun j => T2 x hx j) hux.ne_zero`. Conclude with `⟨i, u, T1 u hu, u', T1 u' hu', huu, hxu⟩`. Introduce `i j u hu u' hu' huu h`.

Establish `h' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j * u` using `h`. Establish `h1` using `le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u hu l) h'`. Establish `h'' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i * u'`. Rewrite using `[h', mul_assoc, huu, mul_one]`. Establish `h2` using `le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u' hu' l) h''`.

Use linear arithmetic over natural numbers and integers.
-/
theorem inert_content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  intro F E _ _ _ _ _ σ _ d b b₂ D hb0 _ hbD v hD _ H1 H2 hno
  have hB0 : Algebra.TensorProduct.basis (Fv F v) b₂ 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, hb0]
    rfl
  have hBD : Algebra.TensorProduct.basis (Fv F v) b₂ 1 * Algebra.TensorProduct.basis (Fv F v) b₂ 1 =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) D) := by
    rw [Algebra.TensorProduct.basis_apply,
      ← Algebra.TensorProduct.includeRight_apply (R := F) (A := Fv F v), ← map_mul, hbD, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hsq : ∀ e : Fv F v, Valued.v e ≤ 1 → ¬ Valued.v (e ^ 2 - algebraMap F (Fv F v) D) < 1 :=
    fun e he hlt => hno ⟨⟨e, he⟩, hlt⟩
  have hfield : IsField (Fv F v ⊗[F] E) :=
    isField (Algebra.TensorProduct.basis (Fv F v) b₂) hB0 hBD
      (fun p q h => norm_ne_zero Valued.v hD hsq h)
  haveI := hfield.nontrivial
  obtain ⟨ϖ, hϖ, hnorm⟩ := exists_unif v
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hincl2 : ∀ j, Algebra.TensorProduct.basis (Fv F v) b₂ j = inclR (Fv F v) (b₂ j) := by
    intro j
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hincl : ∀ k, Algebra.TensorProduct.basis (Fv F v) b k = inclR (Fv F v) (b k) := by
    intro k
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have T1 : ∀ y : Fv F v ⊗[F] E,
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F) → y ∈ intK b v := by
    intro y hy
    simp only [intK, Set.mem_setOf_eq]
    intro k
    exact basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b₂)
      (Algebra.TensorProduct.basis (Fv F v) b) (fun j k => by rw [hincl2]; exact H2 j k) y hy k
  have T2 : ∀ y ∈ intK b v, ∀ j,
      (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F := by
    intro y hy j
    simp only [intK, Set.mem_setOf_eq] at hy
    exact basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b)
      (Algebra.TensorProduct.basis (Fv F v) b₂) (fun k j => by rw [hincl]; exact H1 k j) y hy j
  have hsig : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨hfield, fun i => (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(IsUnit.map _ (Ne.isUnit hϖ0)).pow i, T1 _ fun j => ?_⟩
    dsimp only
    rw [← map_pow, Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul]
    refine (v.adicCompletionIntegers F).mul_mem _ _ ((v.adicCompletionIntegers F).pow_mem hϖO i) ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem
  · intro i
    refine ⟨ϖ ^ (2 * i), ?_, ?_⟩
    · rw [map_pow (algebraMap (Fv F v) (Fv F v ⊗[F] E)), map_pow (sigR (Fv F v) σ), hsig, ← pow_add, two_mul]
    · rw [norm_pow, hnorm, inv_pow]
      simp [qv]
  · intro x hx hux
    obtain ⟨i, u, u', hu, hu', huu, hxu⟩ := exists_factor Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂)
      hϖ hB0 hBD hD hsq x (fun j => T2 x hx j) hux.ne_zero
    exact ⟨i, u, T1 u hu, u', T1 u' hu', huu, hxu⟩
  · intro i j u hu u' hu' huu h
    have h' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j * u := h
    have h1 := le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u hu l) h'
    have h'' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i * u' := by
      rw [h', mul_assoc, huu, mul_one]
    have h2 := le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u' hu' l) h''
    omega

end GlobalTheory.CompanionTheory.SW.QuadField
