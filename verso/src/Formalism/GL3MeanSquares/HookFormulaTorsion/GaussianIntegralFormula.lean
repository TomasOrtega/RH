import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory

/- English proof (translation)
Introduce `ι _ w hw`. Establish `h1 : ∀ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2) = ∏ j, (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2)) j (z j)`. Introduce `z`. Rewrite using `[← Real.exp_sum, ← Finset.sum_neg_distrib]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Establish `h2` using `integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : ι => ℂ) (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2))`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall h1), h2]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (hw j)]`.

Simplify using `[Complex.finrank_real_complex]`.
-/
theorem gaussian_integral_formula : ComplexGaussianIntegral := by
  intro ι _ w hw
  have h1 : ∀ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2) =
      ∏ j, (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2)) j (z j) := by
    intro z
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : ι => ℂ)
    (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2))
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), h2]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (hw j)]
  simp [Complex.finrank_real_complex]

/- English proof (translation)
Introduce `n t₀ Q hn ht hQ`. Establish `hb : 0 < Q / t₀ ^ 2` using `by positivity`. Establish `key` using `_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) - 1) (b := Q / t₀ ^ 2) (by norm_num) (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn linarith) hb`. Establish `hcongr : ∫ t in Set.Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-((t / t₀) ^ 2 * Q)) = ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) - 1) * Real.exp (-(Q / t₀ ^ 2) * x ^ (2 : ℝ))`. Use `setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)` and prove the remaining obligations.

Establish `e1 : t ^ ((n : ℝ) - 1) = t ^ (n - 1)`. Rewrite using `[← Real.rpow_natCast]`. Use `congr 1`. Rewrite using `[Nat.cast_sub hn]`. Simplify using the standard rewrite rules.

Establish `e2 : t ^ (2 : ℝ) = t ^ 2`. Rewrite using `[← Real.rpow_natCast]`. Evaluate the numerical expressions. Simplify using `only [e1, e2]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hcongr, key]`. Establish `e3 : -((n : ℝ) - 1 + 1) / 2 = -((n : ℝ) / 2)` using `by ring`. Establish `e4 : ((n : ℝ) - 1 + 1) / 2 = (n : ℝ) / 2` using `by ring`. Rewrite using `[e3, e4, Real.rpow_neg hb.le, Real.div_rpow hQ.le (by positivity)]`.

Establish `e5 : (t₀ ^ 2) ^ ((n : ℝ) / 2) = t₀ ^ n`. Rewrite using `[← Real.rpow_natCast t₀ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast t₀ n]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e5]`. Establish `hQn : 0 < Q ^ ((n : ℝ) / 2)` using `Real.rpow_pos_of_pos hQ _`. Clear the denominators using the available nonvanishing facts.
-/
theorem gaussian_ray_integral' : GaussianRayIntegral := by
  intro n t₀ Q hn ht hQ
  have hb : 0 < Q / t₀ ^ 2 := by positivity
  have key := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) - 1) (b := Q / t₀ ^ 2)
    (by norm_num) (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                      linarith) hb
  have hcongr : ∫ t in Set.Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-((t / t₀) ^ 2 * Q)) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) - 1) * Real.exp (-(Q / t₀ ^ 2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have e1 : t ^ ((n : ℝ) - 1) = t ^ (n - 1) := by
      rw [← Real.rpow_natCast]
      congr 1
      rw [Nat.cast_sub hn]; simp
    have e2 : t ^ (2 : ℝ) = t ^ 2 := by
      rw [← Real.rpow_natCast]; norm_num
    simp only [e1, e2]
    congr 2
    field_simp
  rw [hcongr, key]
  have e3 : -((n : ℝ) - 1 + 1) / 2 = -((n : ℝ) / 2) := by ring
  have e4 : ((n : ℝ) - 1 + 1) / 2 = (n : ℝ) / 2 := by ring
  rw [e3, e4, Real.rpow_neg hb.le, Real.div_rpow hQ.le (by positivity)]
  have e5 : (t₀ ^ 2) ^ ((n : ℝ) / 2) = t₀ ^ n := by
    rw [← Real.rpow_natCast t₀ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast t₀ n]
    congr 1
    push_cast; ring
  rw [e5]
  have hQn : 0 < Q ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hQ _
  field_simp

/- English proof (translation)
Introduce `n α hn hα`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Use `set β : ℝ := α - ((n : ℝ) - 1) with hβ`. Establish `hβ1 : 1 ≤ β` using `by rw [hβ]; linarith`. Establish `hneg : -β < 0` using `by linarith`.

Establish `hint : IntegrableOn (fun s : ℝ => Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s)) (Set.Ioi 1)` using `(integrableOn_exp_mul_Ioi hneg 1).const_mul _`. Establish `hle : ∫ s in Set.Ioi (1 : ℝ), s ^ (n - 1) * Real.exp (-(α * s)) ≤ ∫ s in Set.Ioi (1 : ℝ), Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s)`. Use `integral_mono_of_nonneg ?_ hint ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))` and prove the remaining obligations. Establish `hs0 : (0 : ℝ) < s` using `lt_trans one_pos hs`.

Simplify using `only [Pi.zero_apply]`. Check the signs of the components of the expression. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))` and prove the remaining obligations. Establish `hs0 : (0 : ℝ) < s` using `lt_trans one_pos hs`. Establish `h1 : s ≤ Real.exp (s - 1)` using `by have := Real.add_one_le_exp (s - 1); linarith`.

Establish `h2 : s ^ (n - 1) ≤ Real.exp (((n : ℝ) - 1) * (s - 1))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul, Nat.cast_sub hn]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Rewrite using `[hβ]`. Expand and normalize the polynomial expressions, which then agree. Use `hle.trans ?_` and prove the remaining obligations.

Rewrite using `[integral_const_mul, integral_exp_mul_Ioi hneg 1]`. Establish `e : Real.exp (-((n : ℝ) - 1)) * (-Real.exp (-β * 1) / -β) = Real.exp (-α) / β`. Rewrite using `[neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]`. Use `congr 2`. Rewrite using `[hβ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `div_le_self (Real.exp_pos _).le hβ1`.
-/
theorem exponential_tail_integral : ExponentialTailIntegral := by
  intro n α hn hα
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := α - ((n : ℝ) - 1) with hβ
  have hβ1 : 1 ≤ β := by rw [hβ]; linarith
  have hneg : -β < 0 := by linarith
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s)) (Set.Ioi 1) :=
    (integrableOn_exp_mul_Ioi hneg 1).const_mul _
  have hle : ∫ s in Set.Ioi (1 : ℝ), s ^ (n - 1) * Real.exp (-(α * s)) ≤
      ∫ s in Set.Ioi (1 : ℝ), Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s) := by
    refine integral_mono_of_nonneg ?_ hint ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
      have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
      simp only [Pi.zero_apply]
      positivity
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
      have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
      have h1 : s ≤ Real.exp (s - 1) := by have := Real.add_one_le_exp (s - 1); linarith
      have h2 : s ^ (n - 1) ≤ Real.exp (((n : ℝ) - 1) * (s - 1)) := by
        calc s ^ (n - 1) ≤ Real.exp (s - 1) ^ (n - 1) := pow_le_pow_left₀ hs0.le h1 _
          _ = Real.exp (((n : ℝ) - 1) * (s - 1)) := by
              rw [← Real.exp_nat_mul, Nat.cast_sub hn]; simp
      calc s ^ (n - 1) * Real.exp (-(α * s))
          ≤ Real.exp (((n : ℝ) - 1) * (s - 1)) * Real.exp (-(α * s)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hβ]; ring
  refine hle.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi hneg 1]
  have e : Real.exp (-((n : ℝ) - 1)) * (-Real.exp (-β * 1) / -β) = Real.exp (-α) / β := by
    rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
    congr 2; rw [hβ]; ring
  rw [e]
  exact div_le_self (Real.exp_pos _).le hβ1

/- English proof (translation)
Introduce `p q N d dτ c c₀ lamAbs hd hdτ hc hc₀ hl hN h1 h2`. Use `set n := p * q with hn`. Establish `hNR : (0 : ℝ) < N` using `by exact_mod_cast (lt_of_lt_of_le one_pos hN)`. Establish `hπ : 0 < Real.pi ^ n` using `pow_pos Real.pi_pos _`. Establish `hcπ : 1 ≤ c * Real.pi ^ n`.

Rewrite `h1` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : (0 : ℝ) < (n.factorial : ℝ)` using `by exact_mod_cast n.factorial_pos`. Use `set A : ℝ := (c₀ / (2 * N * lamAbs)) ^ n with hA`. Use `set B : ℝ := (2 * N * lamAbs / c₀) ^ n with hB`.

Establish `hApos : 0 < A` using `by positivity`. Establish `hBpos : 0 < B` using `by positivity`. Establish `hAB : A * B = 1`. Rewrite using `[hA, hB, ← mul_pow]`. Establish `: c₀ / (2 * N * lamAbs) * (2 * N * lamAbs / c₀) = 1` using `by field_simp`.

Rewrite using `[this, one_pow]`. Establish `h3 : A / (n.factorial : ℝ) * (dτ / 4) ≤ dτ ^ 2 / d`. Use `le_trans ?_ h2` and prove the remaining obligations. Establish `: c * (Real.pi ^ n * A / (n.factorial : ℝ)) * (dτ / 4) = (c * Real.pi ^ n) * (A / (n.factorial : ℝ) * (dτ / 4))` using `by ring`. Rewrite using `[this]`.

Conclude with `le_mul_of_one_le_left (by positivity) hcπ`. Establish `h4 : d * A ≤ 4 * dτ * (n.factorial : ℝ)`. Rewrite `h3` using `[le_div_iff₀ hd]`. Establish `h5 : A / (n.factorial : ℝ) * (dτ / 4) * d = (d * A) * (dτ / (4 * (n.factorial : ℝ)))`. Clear the denominators using the available nonvanishing facts.

Rewrite `h3` using `[h5]`. Establish `h6 : 0 < dτ / (4 * (n.factorial : ℝ))` using `by positivity`. Establish `h7 : dτ ^ 2 = (4 * dτ * (n.factorial : ℝ)) * (dτ / (4 * (n.factorial : ℝ)))`. Clear the denominators using the available nonvanishing facts. Rewrite `h3` using `[h7]`.

Conclude with `le_of_mul_le_mul_right h3 h6`. Establish `h8 : d ≤ 4 * dτ * (n.factorial : ℝ) * B`. Combine the equalities or inequalities in the displayed calculation. Establish `h9 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n` using `by exact_mod_cast Nat.factorial_le_pow n`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hB, mul_assoc, ← mul_pow]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.
-/
theorem joint_upper_bound : DegreeLeMulPowSignatureBound := by
  intro p q N d dτ c c₀ lamAbs hd hdτ hc hc₀ hl hN h1 h2
  set n := p * q with hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le one_pos hN)
  have hπ : 0 < Real.pi ^ n := pow_pos Real.pi_pos _
  have hcπ : 1 ≤ c * Real.pi ^ n := by
    rw [div_le_iff₀ hc] at h1; linarith
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  set A : ℝ := (c₀ / (2 * N * lamAbs)) ^ n with hA
  set B : ℝ := (2 * N * lamAbs / c₀) ^ n with hB
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hAB : A * B = 1 := by
    rw [hA, hB, ← mul_pow]
    have : c₀ / (2 * N * lamAbs) * (2 * N * lamAbs / c₀) = 1 := by field_simp
    rw [this, one_pow]
  have h3 : A / (n.factorial : ℝ) * (dτ / 4) ≤ dτ ^ 2 / d := by
    refine le_trans ?_ h2
    have : c * (Real.pi ^ n * A / (n.factorial : ℝ)) * (dτ / 4) =
        (c * Real.pi ^ n) * (A / (n.factorial : ℝ) * (dτ / 4)) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hcπ
  have h4 : d * A ≤ 4 * dτ * (n.factorial : ℝ) := by
    rw [le_div_iff₀ hd] at h3
    have h5 : A / (n.factorial : ℝ) * (dτ / 4) * d = (d * A) * (dτ / (4 * (n.factorial : ℝ))) := by
      field_simp
    rw [h5] at h3
    have h6 : 0 < dτ / (4 * (n.factorial : ℝ)) := by positivity
    have h7 : dτ ^ 2 = (4 * dτ * (n.factorial : ℝ)) * (dτ / (4 * (n.factorial : ℝ))) := by
      field_simp
    rw [h7] at h3
    exact le_of_mul_le_mul_right h3 h6
  have h8 : d ≤ 4 * dτ * (n.factorial : ℝ) * B := by
    calc d = d * A * B := by rw [mul_assoc, hAB, mul_one]
      _ ≤ 4 * dτ * (n.factorial : ℝ) * B := mul_le_mul_of_nonneg_right h4 hBpos.le
  have h9 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc d ≤ 4 * dτ * (n.factorial : ℝ) * B := h8
    _ ≤ 4 * dτ * (n : ℝ) ^ n * B := by gcongr
    _ = 4 * dτ * (2 / c₀ * (n : ℝ) * N * lamAbs) ^ n := by
        rw [hB, mul_assoc, ← mul_pow]
        congr 2
        field_simp

/- English proof (translation)
Introduce `C₁ C₂ hC₁ hC₂`. Use `⟨8 * C₁ * C₂ ^ 2, ?_⟩` and prove the remaining obligations. Introduce `p q ε₀ h₀ hp hq he0 he1 hh`. Establish `hpR : (1 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hqR : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`.

Establish `hmN : 1 ≤ min p q` using `le_min hp hq`. Establish `hm : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ)` using `by exact_mod_cast hmN`. Use `set m : ℝ := ((min p q : ℕ) : ℝ) with hmdef`. Establish `hPe : ((p * q : ℕ) : ℝ) = (p : ℝ) * q` using `by push_cast; ring`. Establish `hP : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ)` using `by rw [hPe]; nlinarith`.

Use `set P : ℝ := ((p * q : ℕ) : ℝ) with hPdef`. Establish `hNe : ((p + q : ℕ) : ℝ) = (p : ℝ) + q` using `by push_cast; ring`. Establish `hN : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ)` using `by rw [hNe]; linarith`. Use `set N : ℝ := ((p + q : ℕ) : ℝ) with hNdef`. Establish `h2P : ((2 * p * q : ℕ) : ℝ) = 2 * P` using `by rw [hPe]; push_cast; ring`.

Establish `hL : (1 / 2 : ℝ) < Real.log N` using `lt_of_lt_of_le (by have := Real.log_two_gt_d9; linarith) (Real.log_le_log (by norm_num) hN)`. Use `set L : ℝ := Real.log N with hLdef`. Establish `hlog : Real.log (2 * P) ≤ 2 * L`. Establish `: 2 * P ≤ N ^ 2` using `by rw [hPe, hNe]; nlinarith [sq_nonneg ((p : ℝ) - q)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `he2 : 0 < ε₀ ^ 2` using `by positivity`. Establish `hh' : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L ≤ h₀ * ε₀ ^ 2`. Rewrite `hh` using `[div_le_iff₀ he2]`. Then use the resulting hypothesis. Establish `hC₂0 : 0 < C₂` using `by linarith`. Establish `hP0 : 0 < P` using `by linarith`.

Establish `hm0 : 0 < m` using `by linarith`. Establish `hN0 : 0 < N` using `by linarith`. Establish `hL0 : 0 < L` using `by linarith`. Rewrite using `[h2P]`. Prove the components needed by the constructor for the conclusion.

Establish `e : h₀ * (ε₀ / (C₂ * P)) ^ 2 / (4 * m) = (h₀ * ε₀ ^ 2) / (4 * m * C₂ ^ 2 * P ^ 2)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, le_div_iff₀ (by positivity)]`. Use `le_trans ?_ hh'` and prove the remaining obligations. Establish `h1 : C₁ * (2 * P) * Real.log (2 * P) * (4 * m * C₂ ^ 2 * P ^ 2) ≤ C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2)` using `by gcongr`.

Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2) = (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * 2` using `by ring`. Establish `h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * N` using `by ring`. Rewrite using `[h2, h3]`. Conclude with `mul_le_mul_of_nonneg_left hN (by positivity)`.

Establish `e : ε₀ / (C₂ * P) * h₀ / 2 = (h₀ * ε₀ ^ 2) / (2 * C₂ * P * ε₀)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, le_div_iff₀ (by positivity)]`. Use `le_trans ?_ hh'` and prove the remaining obligations. Establish `h1 : C₁ * N * (2 * C₂ * P * ε₀) ≤ C₁ * N * (2 * C₂ * P * (1 / 2))` using `by gcongr`.

Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : C₁ * N * (2 * C₂ * P * (1 / 2)) = (C₁ * N * C₂ * P) * 1` using `by ring`. Establish `h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (C₁ * N * C₂ * P) * (8 * C₂ * m * P ^ 2 * L)` using `by ring`. Rewrite using `[h2, h3]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Establish `h4 : (1 : ℝ) ≤ C₂ * m * P ^ 2`. Establish `: (1 : ℝ) ≤ P ^ 2` using `one_le_pow₀ hP`. Establish `h5 : (1 : ℝ) ≤ C₂ * m` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem parameter_choice_bounds : ThresholdConstantRescaledEpsilonBounds := by
  intro C₁ C₂ hC₁ hC₂
  refine ⟨8 * C₁ * C₂ ^ 2, ?_⟩
  intro p q ε₀ h₀ hp hq he0 he1 hh
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmN : 1 ≤ min p q := le_min hp hq
  have hm : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) := by exact_mod_cast hmN
  set m : ℝ := ((min p q : ℕ) : ℝ) with hmdef
  have hPe : ((p * q : ℕ) : ℝ) = (p : ℝ) * q := by push_cast; ring
  have hP : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by rw [hPe]; nlinarith
  set P : ℝ := ((p * q : ℕ) : ℝ) with hPdef
  have hNe : ((p + q : ℕ) : ℝ) = (p : ℝ) + q := by push_cast; ring
  have hN : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by rw [hNe]; linarith
  set N : ℝ := ((p + q : ℕ) : ℝ) with hNdef
  have h2P : ((2 * p * q : ℕ) : ℝ) = 2 * P := by rw [hPe]; push_cast; ring
  have hL : (1 / 2 : ℝ) < Real.log N :=
    lt_of_lt_of_le (by have := Real.log_two_gt_d9; linarith) (Real.log_le_log (by norm_num) hN)
  set L : ℝ := Real.log N with hLdef
  have hlog : Real.log (2 * P) ≤ 2 * L := by
    have : 2 * P ≤ N ^ 2 := by rw [hPe, hNe]; nlinarith [sq_nonneg ((p : ℝ) - q)]
    calc Real.log (2 * P) ≤ Real.log (N ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have he2 : 0 < ε₀ ^ 2 := by positivity
  have hh' : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L ≤ h₀ * ε₀ ^ 2 := by
    rwa [div_le_iff₀ he2] at hh
  have hC₂0 : 0 < C₂ := by linarith
  have hP0 : 0 < P := by linarith
  have hm0 : 0 < m := by linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := by linarith
  rw [h2P]
  constructor
  · have e : h₀ * (ε₀ / (C₂ * P)) ^ 2 / (4 * m) = (h₀ * ε₀ ^ 2) / (4 * m * C₂ ^ 2 * P ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    refine le_trans ?_ hh'
    have h1 : C₁ * (2 * P) * Real.log (2 * P) * (4 * m * C₂ ^ 2 * P ^ 2) ≤
        C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2) := by gcongr
    refine h1.trans ?_
    have h2 : C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2) =
        (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * 2 := by ring
    have h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * N := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left hN (by positivity)
  · have e : ε₀ / (C₂ * P) * h₀ / 2 = (h₀ * ε₀ ^ 2) / (2 * C₂ * P * ε₀) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    refine le_trans ?_ hh'
    have h1 : C₁ * N * (2 * C₂ * P * ε₀) ≤ C₁ * N * (2 * C₂ * P * (1 / 2)) := by gcongr
    refine h1.trans ?_
    have h2 : C₁ * N * (2 * C₂ * P * (1 / 2)) = (C₁ * N * C₂ * P) * 1 := by ring
    have h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (C₁ * N * C₂ * P) * (8 * C₂ * m * P ^ 2 * L) := by ring
    rw [h2, h3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 : (1 : ℝ) ≤ C₂ * m * P ^ 2 := by
      have : (1 : ℝ) ≤ P ^ 2 := one_le_pow₀ hP
      have h5 : (1 : ℝ) ≤ C₂ * m := by nlinarith
      nlinarith
    nlinarith

/- English proof (translation)
Set `f1 : Fin N → Fin N → ℕ` to `fun a b => if a < b ∧ sg a = true ∧ sg b = false then 1 else 0`. Set `f2 : Fin N → Fin N → ℕ` to `fun a b => if a < b ∧ sg a = false ∧ sg b = true then 1 else 0`. Establish `hL : ∀ a, (univ.filter (fun b => a < b ∧ sg a ≠ sg b)).card = ∑ b, (f1 a b + f2 a b)`. Introduce `a`. Rewrite using `[Finset.card_filter]`.

Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [f1, f2]`. Apply the tactic sequence `cases sg a <;> cases sg b <;> simp`. Establish `hR : (univ.filter (fun a => sg a = true)).card * (univ.filter (fun a => sg a = false)).card = ∑ a, ∑ b, (f1 a b + f2 b a)`. Rewrite using `[Finset.card_filter, Finset.card_filter, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Simplify using `only [f1, f2]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `h' : ¬ b < a` using `not_lt.mpr h.le`. Apply the tactic sequence `cases sg a <;> cases sg b <;> simp [h, h']`.

Substitute `h` using the available equality. Apply the tactic sequence `cases sg a <;> simp`. Establish `h' : ¬ a < b` using `not_lt.mpr h.le`. Apply the tactic sequence `cases sg a <;> cases sg b <;> simp [h, h']`. Rewrite using `[hR]`.

Repeatedly rewrite using `[hL, Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_comm`.
-/
private lemma gl5t1_count (N : ℕ) (sg : Fin N → Bool) :
    ∑ a, (univ.filter (fun b => a < b ∧ sg a ≠ sg b)).card =
      (univ.filter (fun a => sg a = true)).card * (univ.filter (fun a => sg a = false)).card := by
  classical
  let f1 : Fin N → Fin N → ℕ := fun a b => if a < b ∧ sg a = true ∧ sg b = false then 1 else 0
  let f2 : Fin N → Fin N → ℕ := fun a b => if a < b ∧ sg a = false ∧ sg b = true then 1 else 0
  have hL : ∀ a, (univ.filter (fun b => a < b ∧ sg a ≠ sg b)).card = ∑ b, (f1 a b + f2 a b) := by
    intro a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [f1, f2]
    cases sg a <;> cases sg b <;> simp
  have hR : (univ.filter (fun a => sg a = true)).card * (univ.filter (fun a => sg a = false)).card =
      ∑ a, ∑ b, (f1 a b + f2 b a) := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [f1, f2]
    rcases lt_trichotomy a b with h | h | h
    · have h' : ¬ b < a := not_lt.mpr h.le
      cases sg a <;> cases sg b <;> simp [h, h']
    · subst h
      cases sg a <;> simp
    · have h' : ¬ a < b := not_lt.mpr h.le
      cases sg a <;> cases sg b <;> simp [h, h']
  rw [hR]
  simp_rw [hL, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/- English proof (translation)
Introduce `N lam sg d dτ c ε₀ Z hlam p q nab hd hc he0 he1 hZ hZle hc' hτ h12`. Use `set Fp : ℝ := ∏ i ∈ range p, (i.factorial : ℝ) with hFp`. Use `set Fq : ℝ := ∏ i ∈ range q, (i.factorial : ℝ) with hFq`. Use `set FN : ℝ := ∏ i ∈ range N, (i.factorial : ℝ) with hFN`. Establish `hFp0 : 0 < Fp` using `Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)`.

Establish `hFq0 : 0 < Fq` using `Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)`. Establish `hFN0 : 0 < FN` using `Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)`. Use `set Pc : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b + (nab a b : ℝ)) with hPc`. Use `set Pc0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b) with hPc0`. Use `set Pn : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b), (lam a - lam b + ((b.val : ℝ) - a.val)) with hPn`.

Use `set Pn0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b), (lam a - lam b) with hPn0`. Establish `hPc0pos : 0 < Pc0` using `Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by`. Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith))`. Establish `hPn0pos : 0 < Pn0` using `Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by`.

Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith))`. Establish `hPcle : Pc0 ≤ Pc` using `Finset.prod_le_prod (fun a _ => Finset.prod_nonneg (fun b hb => by`. Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith))`.

Use the proof step `(fun a _ => Finset.prod_le_prod (fun b hb => by`. Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith)`. Use the proof step `(fun b _ => by`. Establish `: (0 : ℝ) ≤ (nab a b : ℝ)` using `Nat.cast_nonneg _`.

Use the proof step `linarith))`. Establish `hPnle : Pn0 ≤ Pn` using `Finset.prod_le_prod (fun a _ => Finset.prod_nonneg (fun b hb => by`. Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith))`. Use the proof step `(fun a _ => Finset.prod_le_prod (fun b hb => by`.

Use `hlam a b (Finset.mem_filter.mp hb).2.1` as an intermediate fact. Use the proof step `linarith)`. Use the proof step `(fun b hb => by`. Establish `h : a < b` using `(Finset.mem_filter.mp hb).2.1`. Establish `: (a.val : ℝ) ≤ (b.val : ℝ)` using `by exact_mod_cast h.le`.

Use the proof step `linarith))`. Establish `hall : (∏ a, ∏ b ∈ univ.filter (fun b => a < b), (lam a - lam b)) = Pc0 * Pn0`. Rewrite using `[hPc0, hPn0, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b => a < b)) (fun b => sg a = sg b), Finset.filter_filter, Finset.filter_filter]`.

Establish `hπ : (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b), Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))) = Real.pi ^ (p * q) / Pn`. Repeatedly rewrite using `[Finset.prod_div_distrib, Finset.prod_const]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, gl5t1_count]`. Establish `hPcpos : 0 < Pc` using `lt_of_lt_of_le hPc0pos hPcle`. Establish `hPnpos : 0 < Pn` using `lt_of_lt_of_le hPn0pos hPnle`.

Establish `hπpos : 0 < Real.pi ^ (p * q)` using `pow_pos Real.pi_pos _`. Establish `hceq : c = FN / (Real.pi ^ (p * q) * (Fp * Fq))`. Establish `h1 : c = 1 / (1 / c)` using `by field_simp`. Rewrite using `[h1, hc']`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hall]`. Rewrite `h12` using `[hπ, hτ, hceq]`. Establish `e : FN / (Real.pi ^ (p * q) * (Fp * Fq)) / (Pc / (Fp * Fq)) * (Real.pi ^ (p * q) / Pn) * Z = FN * Z / (Pc * Pn)`. Clear the denominators using the available nonvanishing facts. Rewrite `h12` using `[e]`.

Establish `h1e : 0 < 1 - ε₀` using `by linarith`. Establish `hZ' : (1 - ε₀) * Z ≤ 1`. Use `mul_le_mul_of_nonneg_left hZle h1e.le` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ h1e.ne']`. Then use the resulting hypothesis. Establish `h2 : Pc * Pn ≤ d * (FN * Z)`.

Rewrite `h12` using `[div_le_div_iff₀ hd (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : Pc0 * Pn0 ≤ Pc * Pn` using `mul_le_mul hPcle hPnle hPn0pos.le hPcpos.le`. Rewrite using `[← mul_div_assoc, div_le_iff₀ hFN0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem joint_lower_bound : JointLowerBound := by
  intro N lam sg d dτ c ε₀ Z hlam p q nab hd hc he0 he1 hZ hZle hc' hτ h12
  set Fp : ℝ := ∏ i ∈ range p, (i.factorial : ℝ) with hFp
  set Fq : ℝ := ∏ i ∈ range q, (i.factorial : ℝ) with hFq
  set FN : ℝ := ∏ i ∈ range N, (i.factorial : ℝ) with hFN
  have hFp0 : 0 < Fp := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  have hFq0 : 0 < Fq := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  have hFN0 : 0 < FN := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  set Pc : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b + (nab a b : ℝ)) with hPc
  set Pc0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b) with hPc0
  set Pn : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b),
    (lam a - lam b + ((b.val : ℝ) - a.val)) with hPn
  set Pn0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b), (lam a - lam b) with hPn0
  have hPc0pos : 0 < Pc0 := Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by
    have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
  have hPn0pos : 0 < Pn0 := Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by
    have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
  have hPcle : Pc0 ≤ Pc := Finset.prod_le_prod
    (fun a _ => Finset.prod_nonneg (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
    (fun a _ => Finset.prod_le_prod (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith)
      (fun b _ => by
        have : (0 : ℝ) ≤ (nab a b : ℝ) := Nat.cast_nonneg _
        linarith))
  have hPnle : Pn0 ≤ Pn := Finset.prod_le_prod
    (fun a _ => Finset.prod_nonneg (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
    (fun a _ => Finset.prod_le_prod (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith)
      (fun b hb => by
        have h : a < b := (Finset.mem_filter.mp hb).2.1
        have : (a.val : ℝ) ≤ (b.val : ℝ) := by exact_mod_cast h.le
        linarith))
  have hall : (∏ a, ∏ b ∈ univ.filter (fun b => a < b), (lam a - lam b)) = Pc0 * Pn0 := by
    rw [hPc0, hPn0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b => a < b)) (fun b => sg a = sg b),
      Finset.filter_filter, Finset.filter_filter]
  have hπ : (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b),
      Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))) = Real.pi ^ (p * q) / Pn := by
    simp_rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [Finset.prod_pow_eq_pow_sum, gl5t1_count]
  have hPcpos : 0 < Pc := lt_of_lt_of_le hPc0pos hPcle
  have hPnpos : 0 < Pn := lt_of_lt_of_le hPn0pos hPnle
  have hπpos : 0 < Real.pi ^ (p * q) := pow_pos Real.pi_pos _
  have hceq : c = FN / (Real.pi ^ (p * q) * (Fp * Fq)) := by
    have h1 : c = 1 / (1 / c) := by field_simp
    rw [h1, hc']
    field_simp
  rw [hall]
  rw [hπ, hτ, hceq] at h12
  have e : FN / (Real.pi ^ (p * q) * (Fp * Fq)) / (Pc / (Fp * Fq)) * (Real.pi ^ (p * q) / Pn) * Z =
      FN * Z / (Pc * Pn) := by
    field_simp
  rw [e] at h12
  have h1e : 0 < 1 - ε₀ := by linarith
  have hZ' : (1 - ε₀) * Z ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hZle h1e.le
    rwa [mul_inv_cancel₀ h1e.ne'] at this

  have h2 : Pc * Pn ≤ d * (FN * Z) := by
    rw [div_le_div_iff₀ hd (by positivity)] at h12
    linarith
  have h3 : Pc0 * Pn0 ≤ Pc * Pn := mul_le_mul hPcle hPnle hPn0pos.le hPcpos.le
  rw [← mul_div_assoc, div_le_iff₀ hFN0]
  calc (1 - ε₀) * (Pc0 * Pn0) ≤ (1 - ε₀) * (d * (FN * Z)) :=
        mul_le_mul_of_nonneg_left (h3.trans h2) h1e.le
    _ = (d * FN) * ((1 - ε₀) * Z) := by ring
    _ ≤ (d * FN) * 1 := mul_le_mul_of_nonneg_left hZ' (by positivity)
    _ = d * FN := mul_one _

end Formalism.HermitianLattices.GenusMassVolumes
