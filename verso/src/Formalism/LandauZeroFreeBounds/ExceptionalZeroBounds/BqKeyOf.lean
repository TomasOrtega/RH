import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.IteratedDerivLseriesAlternatingNonneg

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `h3 : (0 : ℝ) ≤ 3 * q` using `by positivity`. Establish `hl0 : 0 ≤ Real.log (3 * q)` using `Real.log_nonneg (by linarith)`. Establish `hl : Real.log (3 * q) ≤ 3 * q` using `Real.log_le_self h3`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_le_of_log_bound {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h3 : (0 : ℝ) ≤ 3 * q := by positivity
  have hl0 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hl : Real.log (3 * q) ≤ 3 * q := Real.log_le_self h3
  calc ‖z‖ ≤ CL * Real.log (3 * q) := h
    _ ≤ |CL| * Real.log (3 * q) := mul_le_mul_of_nonneg_right (le_abs_self CL) hl0
    _ ≤ |CL| * (3 * q) := mul_le_mul_of_nonneg_left hl (abs_nonneg CL)

/- English proof (translation)
Establish `hl43 : 0 < Real.log (4 / 3 : ℝ)` using `Real.log_pos (by norm_num)`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hx0 : 0 ≤ Real.log T / Real.log (4 / 3)` using `div_nonneg (Real.log_nonneg hT) hl43.le`. Use `⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩` and prove the remaining obligations. Establish `hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ)` using `by push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]`.

Establish `hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)`. Establish `h` using `mul_le_mul_of_nonneg_right hM hl43.le`. Rewrite `h` using `[div_mul_cancel₀ _ hl43.ne']`. Then use the resulting hypothesis. Establish `hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.log_pow, Real.exp_log (by positivity)]`. Establish `h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Combine the linear relations using `[Nat.ceil_lt_add_one hx0]`.
-/
lemma exists_taylor_truncation_order (T : ℝ) (hT : 1 ≤ T) :
    ∃ M : ℕ, 1 ≤ M ∧ T * (3 / 4 : ℝ) ^ M ≤ 1 ∧ (M : ℝ) ≤ Real.log T / Real.log (4 / 3) + 2 := by
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.log T / Real.log (4 / 3) := div_nonneg (Real.log_nonneg hT) hl43.le
  refine ⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩
  · have hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]
    have hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3) := by
      have h := mul_le_mul_of_nonneg_right hM hl43.le
      rwa [div_mul_cancel₀ _ hl43.ne'] at h
    have hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp (((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)) :=
          Real.exp_le_exp.mpr hlog
        _ = (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by positivity
    calc T * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)
        ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) :=
          mul_le_mul_of_nonneg_right hT' hp.le
      _ = 1 := h34
  · push_cast
    linarith [Nat.ceil_lt_add_one hx0]

/- English proof (translation)
Establish `h1 : 0 < 1 - σ` using `by linarith`. Establish `hb : 2 - σ ≤ Real.exp (1 - σ)`. Use `Real.add_one_le_exp (1 - σ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb0 : 0 ≤ 2 - σ` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]`. Use `_ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _`.
-/
lemma two_sub_pow_le_exp {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by
  have h1 : 0 < 1 - σ := by linarith
  have hb : 2 - σ ≤ Real.exp (1 - σ) := by
    have := Real.add_one_le_exp (1 - σ); linarith
  have hb0 : 0 ≤ 2 - σ := by linarith
  calc (2 - σ) ^ M ≤ Real.exp (1 - σ) ^ M := pow_le_pow_left₀ hb0 hb M
    _ = Real.exp (M * (1 - σ)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (A + P * (1 - σ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]
    _ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _

/- English proof (translation)
Introduce `hCoeff hEnt hGrow hL1`. Take `⟨Cg, Kg, hg⟩` from `hGrow`. Take `⟨CL, hL⟩` from `hL1`. Take `⟨c0, hc0def⟩ : ∃ c : ℝ, c = |Cg| + 54 * |CL| ^ 3 + 1` from `⟨_, rfl⟩`. Take `⟨K', hK'def⟩ : ∃ k : ℝ, k = max Kg 2` from `⟨_, rfl⟩`.

Take `⟨ℓ, hℓdef⟩ : ∃ l : ℝ, l = Real.log (4 / 3)` from `⟨_, rfl⟩`. Establish `hℓ : 0 < ℓ` using `by rw [hℓdef]; exact Real.log_pos (by norm_num)`. Establish `hc0 : 1 ≤ c0`. Rewrite using `[hc0def]`. Use `abs_nonneg Cg` as an intermediate fact.

Use `pow_nonneg (abs_nonneg CL) 3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKgK : Kg ≤ K'` using `by rw [hK'def]; exact le_max_left _ _`. Establish `h2K : (2 : ℝ) ≤ K'` using `by rw [hK'def]; exact le_max_right _ _`. Use `⟨Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)), K' / ℓ, div_nonneg (by linarith) hℓ.le, ?_⟩` and prove the remaining obligations.

Introduce `q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h1ne h2ne hψne hψ σ hσ1 hσ2`. Establish `h1σ : 0 < 1 - σ` using `by linarith`. Establish `hq₁ : (1 : ℝ) ≤ q₁` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)`. Establish `hq₂ : (1 : ℝ) ≤ q₂` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)`. Establish `hN : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂` using `by push_cast; ring`.

Establish `hN1 : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ)` using `by rw [hN]; nlinarith`. Take `⟨a, ha0, ha1, habs, hFa⟩` from `hCoeff q₁ q₂ χ₁ χ₂ ψ h1 h2 hψ`. Take `⟨G, hG, hFG⟩` from `hEnt q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne`. Establish `hlam : ‖lamBq χ₁ χ₂ ψ‖ ≤ 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2`. Establish `e1` using `norm_le_of_log_bound q₁ (hL q₁ χ₁ h1ne)`.

Establish `e2` using `norm_le_of_log_bound q₂ (hL q₂ χ₂ h2ne)`. Establish `e3` using `norm_le_of_log_bound (q₁ * q₂) (hL (q₁ * q₂) ψ hψne)`. Simplify using `only [lamBq, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hKg : ((q₁ * q₂ : ℕ) : ℝ) ^ Kg ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K'` using `Real.rpow_le_rpow_of_exponent_le hN1 hKgK`.

Establish `hK2 : ((q₁ * q₂ : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K'`. Rewrite using `[← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)`. Establish `hNK0 : 0 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K'` using `by positivity`. Establish `hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K'`. Introduce `s hs`.

Rewrite `hs` using `[mem_sphere_iff_norm]`. Establish `hs1 : s ≠ 1` using `by rintro rfl; norm_num at hs`. Establish `hd : (1 / 2 : ℝ) ≤ ‖s - 1‖`. Establish `h` using `norm_sub_le (s - 1) (1 : ℂ)`. Establish `e : s - 1 - 1 = s - 2` using `by ring`.

Rewrite `h` using `[e, hs, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGs : G s = Fbq χ₁ χ₂ ψ s - lamBq χ₁ χ₂ ψ / (s - 1)` using `by rw [hFG s hs1]; ring`. Establish `hF` using `hg q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne s hs`. Establish `hdiv : ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ ≤ 2 * ‖lamBq χ₁ χ₂ ψ‖`.

Rewrite using `[norm_div, div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[norm_nonneg (lamBq χ₁ χ₂ ψ)]`. Establish `hc3 : 0 ≤ 54 * |CL| ^ 3` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc0def]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right (le_abs_self Cg) (by positivity : (0 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ Kg), mul_le_mul_of_nonneg_left hKg (abs_nonneg Cg), mul_le_mul_of_nonneg_left hK2 hc3]`. Establish `hNK1 : 1 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K'` using `Real.one_le_rpow hN1 (by linarith)`. Establish `hT : 1 ≤ 8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')`. Use polynomial arithmetic with `[mul_le_mul hc0 hNK1 zero_le_one (by linarith)]`. Take `⟨M, hM1, hTM, hMle⟩` from `exists_taylor_truncation_order _ hT`.

Rewrite `hMle` using `[← hℓdef]`. Establish `hcore` using `lseries_taylor_lower_bound ha0 ha1 habs hG hFa hFG hB hσ1 hσ2 hM1`. Establish `hpow` using `two_sub_pow_le_exp (A := 2) (P := Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ) (M := M) (by norm_num) hσ1 hσ2 (by linarith)`. Establish `hlogT : Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) = Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)`. Rewrite using `[← mul_assoc, Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by linarith) _).ne', Real.log_rpow (by linarith)]`.

Establish `hlogc : 0 ≤ Real.log (8 * c0)` using `Real.log_nonneg (by linarith)`. Establish `hexp : Real.exp (Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ * (1 - σ)) ≤ Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ))`. Rewrite using `[Real.rpow_def_of_pos (show (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) by linarith) (K' / ℓ * (1 - σ)), ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[hlogT]`.

Establish `eL : (Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)) / ℓ * (1 - σ) = (Real.log (8 * c0) * (1 - σ) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ` using `by ring`. Establish `eR : Real.log (8 * c0) / (8 * ℓ) + Real.log ((q₁ * q₂ : ℕ) : ℝ) * (K' / ℓ * (1 - σ)) = (Real.log (8 * c0) / 8 + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ` using `by ring`. Rewrite using `[eL, eR]`. Apply `div_le_div_of_nonneg_right _ hℓ.le` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1 / 8) hlogc]`.

Establish `hpow' : (2 - σ) ^ M ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ))` using `hpow.trans ((mul_le_mul_of_nonneg_left hexp (Real.exp_pos 2).le).trans_eq (by ring))`. Establish `h34 : 4 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') * (3 / 4 : ℝ) ^ M ≤ 1 / 2` using `by linarith`. Establish `hlam0` using `norm_nonneg (lamBq χ₁ χ₂ ψ)`. Establish `hdiv : ‖lamBq χ₁ χ₂ ψ‖ * (2 - σ) ^ M / (1 - σ) ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) / (1 - σ)`. Apply `div_le_div_of_nonneg_right _ h1σ.le` to reduce the goal to its premises.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hpow' hlam0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem product_lfunction_key_inequality : BqKeyOf := by
  intro hCoeff hEnt hGrow hL1
  obtain ⟨Cg, Kg, hg⟩ := hGrow
  obtain ⟨CL, hL⟩ := hL1
  obtain ⟨c0, hc0def⟩ : ∃ c : ℝ, c = |Cg| + 54 * |CL| ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K', hK'def⟩ : ∃ k : ℝ, k = max Kg 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ l : ℝ, l = Real.log (4 / 3) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by norm_num)
  have hc0 : 1 ≤ c0 := by
    rw [hc0def]; have := abs_nonneg Cg; have := pow_nonneg (abs_nonneg CL) 3; linarith
  have hKgK : Kg ≤ K' := by rw [hK'def]; exact le_max_left _ _
  have h2K : (2 : ℝ) ≤ K' := by rw [hK'def]; exact le_max_right _ _
  refine ⟨Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)), K' / ℓ,
    div_nonneg (by linarith) hℓ.le, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h1ne h2ne hψne hψ σ hσ1 hσ2
  have h1σ : 0 < 1 - σ := by linarith
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : (1 : ℝ) ≤ q₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hN : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by rw [hN]; nlinarith
  obtain ⟨a, ha0, ha1, habs, hFa⟩ := hCoeff q₁ q₂ χ₁ χ₂ ψ h1 h2 hψ
  obtain ⟨G, hG, hFG⟩ := hEnt q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne
  have hlam : ‖lamBq χ₁ χ₂ ψ‖ ≤ 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by
    have e1 := norm_le_of_log_bound q₁ (hL q₁ χ₁ h1ne)
    have e2 := norm_le_of_log_bound q₂ (hL q₂ χ₂ h2ne)
    have e3 := norm_le_of_log_bound (q₁ * q₂) (hL (q₁ * q₂) ψ hψne)
    simp only [lamBq, norm_mul]
    calc _ ≤ (|CL| * (3 * q₁)) * (|CL| * (3 * q₂)) * (|CL| * (3 * ((q₁ * q₂ : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) (by positivity)) e3 (norm_nonneg _) (by positivity)
      _ = 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by rw [hN]; ring
  have hKg : ((q₁ * q₂ : ℕ) : ℝ) ^ Kg ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' :=
    Real.rpow_le_rpow_of_exponent_le hN1 hKgK
  have hK2 : ((q₁ * q₂ : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hNK0 : 0 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by positivity
  have hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    intro s hs
    rw [mem_sphere_iff_norm] at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    have hd : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h := norm_sub_le (s - 1) (1 : ℂ)
      have e : s - 1 - 1 = s - 2 := by ring
      rw [e, hs, norm_one] at h
      linarith
    have hGs : G s = Fbq χ₁ χ₂ ψ s - lamBq χ₁ χ₂ ψ / (s - 1) := by rw [hFG s hs1]; ring
    have hF := hg q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne s hs
    have hdiv : ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ ≤ 2 * ‖lamBq χ₁ χ₂ ψ‖ := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lamBq χ₁ χ₂ ψ)]
    have hc3 : 0 ≤ 54 * |CL| ^ 3 := by positivity
    calc ‖G s‖ ≤ ‖Fbq χ₁ χ₂ ψ s‖ + ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ := by rw [hGs]; exact norm_sub_le _ _
      _ ≤ Cg * ((q₁ * q₂ : ℕ) : ℝ) ^ Kg + 2 * (27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2) := by linarith
      _ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
        rw [hc0def]
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cg) (by positivity : (0 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ Kg),
          mul_le_mul_of_nonneg_left hKg (abs_nonneg Cg), mul_le_mul_of_nonneg_left hK2 hc3]
  have hNK1 : 1 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := Real.one_le_rpow hN1 (by linarith)
  have hT : 1 ≤ 8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') := by
    nlinarith [mul_le_mul hc0 hNK1 zero_le_one (by linarith)]
  obtain ⟨M, hM1, hTM, hMle⟩ := exists_taylor_truncation_order _ hT
  rw [← hℓdef] at hMle
  have hcore := lseries_taylor_lower_bound ha0 ha1 habs hG hFa hFG hB hσ1 hσ2 hM1
  have hpow := two_sub_pow_le_exp (A := 2) (P := Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ)
    (M := M) (by norm_num) hσ1 hσ2 (by linarith)
  have hlogT : Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) =
      Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [← mul_assoc, Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  have hlogc : 0 ≤ Real.log (8 * c0) := Real.log_nonneg (by linarith)
  have hexp : Real.exp (Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ * (1 - σ)) ≤
      Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) by linarith) (K' / ℓ * (1 - σ)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlogT]
    have eL : (Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)) / ℓ * (1 - σ) =
        (Real.log (8 * c0) * (1 - σ) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    have eR : Real.log (8 * c0) / (8 * ℓ) + Real.log ((q₁ * q₂ : ℕ) : ℝ) * (K' / ℓ * (1 - σ)) =
        (Real.log (8 * c0) / 8 + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    rw [eL, eR]
    apply div_le_div_of_nonneg_right _ hℓ.le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1 / 8) hlogc]
  have hpow' : (2 - σ) ^ M ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) *
      ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) :=
    hpow.trans ((mul_le_mul_of_nonneg_left hexp (Real.exp_pos 2).le).trans_eq (by ring))
  have h34 : 4 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') * (3 / 4 : ℝ) ^ M ≤ 1 / 2 := by linarith
  have hlam0 := norm_nonneg (lamBq χ₁ χ₂ ψ)
  have hdiv : ‖lamBq χ₁ χ₂ ψ‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ‖lamBq χ₁ χ₂ ψ‖ *
        ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ h1σ.le
    nlinarith [mul_le_mul_of_nonneg_left hpow' hlam0]
  linarith

end Formalism.ZeroFreeDirichlet
