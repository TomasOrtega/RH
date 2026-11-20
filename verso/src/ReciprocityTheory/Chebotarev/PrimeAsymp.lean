import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum
import ReciprocityTheory.Chebotarev.EulerLim

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem pa_cpow_eq (n : ℕ) (s : ℝ) :
    ((n : ℂ) ^ (-(s : ℂ))) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

/- English proof (translation)
Establish `h : Ideal.absNorm a.1 ≠ 0`. Introduce `h0`. Conclude with `a.2 (Ideal.absNorm_eq_zero_iff.mp h0)`. Conclude with `Nat.one_le_iff_ne_zero.mpr h` after adjusting the coercions.
-/
theorem pa_one_le_absNorm {E : Type} [Field E] [NumberField E] (a : NZIdeal E) :
    (1 : ℝ) ≤ ((Ideal.absNorm a.1 : ℕ) : ℝ) := by
  have h : Ideal.absNorm a.1 ≠ 0 := by
    intro h0
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

/- English proof (translation)
Establish `h` using `two_le_Nrm q`. Establish `h1 : (1 : ℝ) < ((Nrm q : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 < Nrm q)`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)`.
-/
theorem pa_rpow_lt_one {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 0 < s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) < 1 := by
  have h := two_le_Nrm q
  have h1 : (1 : ℝ) < ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < Nrm q)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

/- English proof (translation)
Establish `hs0 : (0 : ℝ) < s` using `by linarith`. Use `set f : Ideal (𝓞 E) → ℂ := fun a => ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)) with hfdef`. Establish `hf1 : f 1 = 1` using `by simp [hfdef]`. Establish `hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b`. Introduce `a b`.

Simplify using `only [hfdef, map_mul, Nat.cast_mul]`. Conclude with `Complex.natCast_mul_natCast_cpow _ _ _`. Establish `hnorm : ∀ a : Ideal (𝓞 E), ‖f a‖ = ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)`. Introduce `a`. Simplify using `only [hfdef]`.

Rewrite using `[pa_cpow_eq, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]`. Establish `hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)`. Simplify using `only [hnorm]`. Conclude with `summable_absNorm_rpow E hs`. Establish `hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1`.

Introduce `q`. Rewrite using `[hnorm]`. Conclude with `pa_rpow_lt_one q hs0`. Establish `h` using `euler_exp_log f hf1 hmul hsum hlt`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_tsum]`. Establish `e1 : (∑' q : Prm E, (((-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ)) = ∑' q : Prm E, -Complex.log (1 - f q.asIdeal)`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Establish `hx` using `pa_rpow_lt_one q hs0`. Rewrite using `[Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one, ← pa_cpow_eq]`.

Both sides reduce to the same expression. Establish `e2 : (∑' a : NZIdeal E, ((((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) = ∑' a : NZIdeal E, f a.1`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[← pa_cpow_eq]`. Rewrite using `[e1, e2]`.

Conclude with `h`.
-/
theorem real_euler (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Real.exp (∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) =
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set f : Ideal (𝓞 E) → ℂ := fun a => ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)) with hfdef
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b := by
    intro a b
    simp only [hfdef, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _
  have hnorm : ∀ a : Ideal (𝓞 E), ‖f a‖ = ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s) := by
    intro a
    simp only [hfdef]
    rw [pa_cpow_eq, Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hsum : Summable (fun a : NZIdeal E => ‖f a.1‖) := by
    simp only [hnorm]
    exact summable_absNorm_rpow E hs
  have hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1 := by
    intro q
    rw [hnorm]
    exact pa_rpow_lt_one q hs0
  have h := euler_exp_log f hf1 hmul hsum hlt
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_tsum]
  have e1 : (∑' q : Prm E, (((-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) : ℝ) : ℂ)) =
      ∑' q : Prm E, -Complex.log (1 - f q.asIdeal) := by
    refine tsum_congr fun q => ?_
    have hx := pa_rpow_lt_one q hs0
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one,
      ← pa_cpow_eq]
    rfl
  have e2 : (∑' a : NZIdeal E, ((((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) = ∑' a : NZIdeal E, f a.1 := by
    refine tsum_congr fun a => ?_
    rw [← pa_cpow_eq]
  rw [e1, e2]
  exact h

/- English proof (translation)
The claim follows from `|-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by have hx1 : |x| < 1 := by rw [abs_of_nonneg hx0] linarith have h := Real.abs_log_sub_add_sum_range_le hx1 1 norm_num at h rw [abs_of_nonneg hx0] at h rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg] calc |x + Real …`.
-/
theorem pa_log_bdd {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg]
  calc |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]

/- English proof (translation)
The claim follows from `|(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤ 2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by have hs0 : (0 : ℝ) < s := by linarith have hP := summable_prm_rpow E hs have h2 := summable_prm_rpow E (by norm_num : (1 : ℝ) < 2) have hb : ∀ q : Prm E, ‖ …`.
-/
theorem pa_A_sub_PE (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    |(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤
      2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hP := summable_prm_rpow E hs
  have h2 := summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ q : Prm E, ‖-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)‖ ≤
      2 * ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have hN2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hN0 : (0 : ℝ) < ((Nrm q : ℕ) : ℝ) := by linarith
    have hx0 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
    have hxh : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
      calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
    rw [Real.norm_eq_abs]
    refine (pa_log_bdd hx0 hxh).trans ?_
    have : (((Nrm q : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hg : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_norm_bounded (h2.mul_left 2) hb
  have hA : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) :=
    (hg.add hP).congr (fun q => by ring)
  unfold PE
  rw [← hA.tsum_sub hP, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((h2.hasSum).mul_left 2) hb

/- English proof (translation)
Establish `h` using `(summable_absNorm_rpow E hs).le_tsum (⟨⊤, top_ne_bot⟩ : NZIdeal E) (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)`. Simplify `h` using `[Ideal.absNorm_top]`.
-/
theorem pa_Z_ge_one (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have h := (summable_absNorm_rpow E hs).le_tsum (⟨⊤, top_ne_bot⟩ : NZIdeal E)
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [Ideal.absNorm_top] using h

/- English proof (translation)
The claim follows from `Summable.tsum_le_tsum (fun a => Real.rpow_le_rpow_of_exponent_le (pa_one_le_absNorm a) (by linarith)) (summable_absNorm_rpow E (lt_of_lt_of_le ht hts)) (summable_absNorm_rpow E ht)`.
-/
theorem pa_Z_anti (E : Type) [Field E] [NumberField E] {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t) :=
  Summable.tsum_le_tsum (fun a => Real.rpow_le_rpow_of_exponent_le (pa_one_le_absNorm a) (by linarith))
    (summable_absNorm_rpow E (lt_of_lt_of_le ht hts)) (summable_absNorm_rpow E ht)

/- English proof (translation)
Establish `h` using `(Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)`. Simplify using `only [Complex.ofReal_re] at h`. Use `h.congr' ?_` and prove the remaining obligations. Use `eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[dedekindZeta_eq_tsum E hs]`. Establish `e : (∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) = ((∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_tsum]`. Conclude with `tsum_congr fun a => pa_cpow_eq _ _`. Rewrite using `[e, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]`.
-/
theorem pa_Z_lim (E : Type) [Field E] [NumberField E] :
    Tendsto (fun s : ℝ => (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue E)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  refine eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_
  simp only [Function.comp_apply]
  rw [dedekindZeta_eq_tsum E hs]
  have e : (∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) =
      ((∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun a => pa_cpow_eq _ _
  rw [e, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]

/- English proof (translation)
Use `set r := dedekindZeta_residue E`. Establish `hr : 0 < r` using `dedekindZeta_residue_pos E`. Establish `hmem` using `pa_Z_lim E (Icc_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 2 * r))`. Take `⟨u, hu, hsub⟩` from `(mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (1 : ℝ) < 2)).mp hmem`. Establish `hu1 : 1 < u` using `hu`.

Use `set t := min ((1 + u) / 2) 2 with htdef`. Establish `ht1 : 1 < t` using `lt_min (by linarith) (by norm_num)`. Establish `htu : t < u` using `lt_of_le_of_lt (min_le_left _ _) (by linarith)`. Establish `ht2 : t ≤ 2` using `min_le_right _ _`. Use `set Zt := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t)`.

Use `⟨min (r / 2) (t - 1), max (2 * r) Zt, lt_min (by linarith) (by linarith), fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨hs1, hs2⟩` from `hs`. Establish `hZ1` using `pa_Z_ge_one E hs1`. Break down `le_total s t with hst | hst` into its components or cases. Establish `hin` using `hsub ⟨hs1, lt_of_le_of_lt hst htu⟩`.

Take `⟨h1, h2⟩` from `hin`. Conclude with `⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩`. Establish `hZ` using `pa_Z_anti E ht1 hst`. Prove the components needed by the constructor for the conclusion. Use `(min_le_right _ _).trans ?_` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hZ0 : 0 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pa_g_bdd (E : Type) [Field E] [NumberField E] :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      m ≤ (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ∧
      (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤ M := by
  set r := dedekindZeta_residue E
  have hr : 0 < r := dedekindZeta_residue_pos E
  have hmem := pa_Z_lim E (Icc_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 2 * r))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (1 : ℝ) < 2)).mp hmem
  have hu1 : 1 < u := hu
  set t := min ((1 + u) / 2) 2 with htdef
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  set Zt := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t)
  refine ⟨min (r / 2) (t - 1), max (2 * r) Zt, lt_min (by linarith) (by linarith), fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have hZ1 := pa_Z_ge_one E hs1
  rcases le_total s t with hst | hst
  · have hin := hsub ⟨hs1, lt_of_le_of_lt hst htu⟩
    obtain ⟨h1, h2⟩ := hin
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have hZ := pa_Z_anti E ht1 hst
    constructor
    · refine (min_le_right _ _).trans ?_
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      have hZ0 : 0 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by linarith
      nlinarith

/- English proof (translation)
Introduce `E _ _`. Take `⟨m, M, hm, hbd⟩` from `pa_g_bdd E`. Use `⟨2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) + (|Real.log m| + |Real.log M|), fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hbd s hs`. Establish `hs1 : 1 < s` using `hs.1`.

Establish `hAP` using `pa_A_sub_PE E hs1`. Establish `hZ` using `pa_Z_ge_one E hs1`. Establish `he` using `real_euler E hs1`. Use `set A := ∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))`. Use `set Z := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)`.

Establish `hAZ : A = Real.log Z` using `by rw [← he, Real.log_exp]`. Establish `hg0 : 0 < (s - 1) * Z` using `lt_of_lt_of_le hm h1`. Establish `hlog : A - Real.log (1 / (s - 1)) = Real.log ((s - 1) * Z)`. Rewrite using `[hAZ, one_div, Real.log_inv, Real.log_mul (by linarith) (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hl1 : Real.log m ≤ Real.log ((s - 1) * Z)` using `Real.log_le_log hm h1`. Establish `hl2 : Real.log ((s - 1) * Z) ≤ Real.log M` using `Real.log_le_log hg0 h2`. Establish `hb : |Real.log ((s - 1) * Z)| ≤ |Real.log m| + |Real.log M|` using `abs_le.mpr ⟨by linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)], by linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]⟩`. Establish `e : PE E s - Real.log (1 / (s - 1)) = -(A - PE E s) + (A - Real.log (1 / (s - 1)))` using `by ring`. Rewrite using `[e, hlog]`.

Use `(abs_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pe_log_bdd : faceMap_castSucc_comp_eq_succ := by
  intro E _ _
  obtain ⟨m, M, hm, hbd⟩ := pa_g_bdd E
  refine ⟨2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) + (|Real.log m| + |Real.log M|), fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hbd s hs
  have hs1 : 1 < s := hs.1
  have hAP := pa_A_sub_PE E hs1
  have hZ := pa_Z_ge_one E hs1
  have he := real_euler E hs1
  set A := ∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))
  set Z := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)
  have hAZ : A = Real.log Z := by rw [← he, Real.log_exp]
  have hg0 : 0 < (s - 1) * Z := lt_of_lt_of_le hm h1
  have hlog : A - Real.log (1 / (s - 1)) = Real.log ((s - 1) * Z) := by
    rw [hAZ, one_div, Real.log_inv, Real.log_mul (by linarith) (by linarith)]
    ring
  have hl1 : Real.log m ≤ Real.log ((s - 1) * Z) := Real.log_le_log hm h1
  have hl2 : Real.log ((s - 1) * Z) ≤ Real.log M := Real.log_le_log hg0 h2
  have hb : |Real.log ((s - 1) * Z)| ≤ |Real.log m| + |Real.log M| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)],
      by linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]⟩
  have e : PE E s - Real.log (1 / (s - 1)) = -(A - PE E s) + (A - Real.log (1 / (s - 1))) := by ring
  rw [e, hlog]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith

end ReciprocityTheory.Cheb
