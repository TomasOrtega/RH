import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

/- English proof (translation)
Unfold `lam`. Establish `h1 : (1 : ℝ) < ℓ` using `by exact_mod_cast (by omega : 1 < ℓ)`. Break down `Nat.eq_zero_or_pos H with rfl | hH` into its components or cases. Simplify using the standard rewrite rules. Establish `h2 : (1 : ℝ) ≤ 2 * (H : ℝ)`.

Establish `: (1 : ℝ) ≤ H` using `by exact_mod_cast hH`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg h1 h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma lam_ge_one (ℓ H : ℕ) (hℓ : 2 ≤ ℓ) : 1 ≤ lam ℓ H := by
  unfold lam
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have h2 : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg h1 h2
    linarith

/- English proof (translation)
Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `hd0 : (0 : ℝ) < x - 1` using `by linarith`. Establish `ht : (0 : ℝ) ≤ x - 11` using `by linarith`. Establish `ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`.

Use polynomial arithmetic with `[pow_nonneg ht 3, pow_nonneg ht 2]`. Establish `hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[pow_nonneg ht 2]`. Establish `hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2`.

Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[pow_nonneg ht 2]`. Establish `hx2 : (0 : ℝ) ≤ 1 / x ^ 2` using `by positivity`. Establish `e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2)` using `by ring`. Establish `e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2)` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma hcoef_le (x : ℝ) (hx : 11 ≤ x) :
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd0 : (0 : ℝ) < x - 1 := by linarith
  have ht : (0 : ℝ) ≤ x - 11 := by linarith
  have ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 2]
  have hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hx2 : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  have e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2) := by ring
  have e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2) := by ring
  linarith

/- English proof (translation)
Introduce `ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2`. Establish `hx : (11 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1` using `by linarith`. Establish `hd0 : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hx0 : (0 : ℝ) < ℓ` using `by linarith`.

Establish `hL` using `lam_ge_one ℓ (h + η) (by omega)`. Establish `hc` using `hcoef_le (ℓ : ℝ) hx`. Establish `hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1`. Unfold `sig`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1)`. Establish `h1` using `Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)`. Rewrite `h1` using `[Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]`. Then use the resulting hypothesis. Rewrite using `[hsig]`.

Unfold `sig₂ at he2 ⊢`. Unfold `aR at ha`. Use `set L := lam ℓ (h + η) with hLdef`. Use `set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef`. Establish `hhH : (h : ℝ) ≤ H`.

Rewrite using `[hHdef]`. Use `push_cast`. Combine the linear relations using `[(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]`. Establish `hbH : (b : ℝ) ≤ H` using `le_trans (by exact_mod_cast hbh) hhH`. Establish `hH0 : 0 ≤ H` using `by positivity`.

Establish `hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2`. Rewrite using `[sq, ← div_div]`. Apply `div_le_div_of_nonneg_right _ hd0.le` to reduce the goal to its premises. Conclude with `hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)`. Establish `hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤ (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1)` using `div_le_div_of_nonneg_right ha hd0.le`.

Establish `hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))` using `div_le_div_of_nonneg_right hbH (by positivity)`. Establish `hHc` using `mul_le_mul_of_nonneg_left hc hH0`. Establish `e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) = H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)`. Rewrite using `[div_div, ← pow_succ, mul_div_assoc]`. Establish `hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10`.

Rewrite using `[div_le_div_iff₀ hd0 (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) hd`. Establish `hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10` using `div_le_div_of_nonneg_left (by positivity) (by norm_num) hd`. Establish `hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1)` using `by positivity`.

Establish `k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) = 2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1)`. Expand and normalize the polynomial expressions, which then agree. Establish `k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) = 3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1))`. Expand and normalize the polynomial expressions, which then agree. Establish `k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) = H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) + L / ((ℓ : ℝ) - 1)`.

Expand and normalize the polynomial expressions, which then agree. Establish `k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) = ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1)`. Expand and normalize the polynomial expressions, which then agree. Establish `k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 + 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) = 8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) + H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))`. Expand and normalize the polynomial expressions, which then agree.

Establish `k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2)` using `by ring`. Establish `k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2)` using `by ring`. Establish `k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1))` using `by ring`. Rewrite `hs1` using `[k1]`. Rewrite `hE` using `[k2]`.

Rewrite `hA` using `[k3]`. Rewrite `hHc` using `[k5]`. Rewrite `he2` using `[k6]`. Rewrite using `[k4, k6, k7, k8]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem expBound_statement : ExpBound := by
  intro ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2
  have hx : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < ℓ := by linarith
  have hL := lam_ge_one ℓ (h + η) (by omega)
  have hc := hcoef_le (ℓ : ℝ) hx
  have hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1 := by
    unfold sig
    push_cast
    ring
  have hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h1
  rw [hsig]
  unfold sig₂ at he2 ⊢
  unfold aR at ha
  set L := lam ℓ (h + η) with hLdef
  set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef
  have hhH : (h : ℝ) ≤ H := by
    rw [hHdef]
    push_cast
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hbH : (b : ℝ) ≤ H := le_trans (by exact_mod_cast hbh) hhH
  have hH0 : 0 ≤ H := by positivity
  have hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [sq, ← div_div]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)
  have hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤
      (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) :=
    div_le_div_of_nonneg_right ha hd0.le
  have hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hbH (by positivity)
  have hHc := mul_le_mul_of_nonneg_left hc hH0
  have e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) =
      H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3) := by
    rw [div_div, ← pow_succ, mul_div_assoc]
  have hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  have hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hd
  have hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
  have hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1) := by positivity
  have k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) =
      2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) =
      3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by
    ring
  have k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) =
      H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) +
        L / ((ℓ : ℝ) - 1) := by
    ring
  have k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) =
      ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 +
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) =
      8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) +
        H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    ring
  have k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2) := by ring
  have k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2) := by ring
  have k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by ring
  rw [k1] at hs1
  rw [k2] at hE
  rw [k3] at hA
  rw [k5] at hHc
  rw [k6] at he2
  rw [k4, k6, k7, k8]
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
