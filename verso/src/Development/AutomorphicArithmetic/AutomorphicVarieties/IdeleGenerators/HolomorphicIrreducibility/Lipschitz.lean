import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open Polynomial Filter Topology

namespace UpperTheory.V.Sd

/- English proof (translation)
Establish `hx' : (1 : ℂ) - x ≠ 0` using `sub_ne_zero.mpr (Ne.symm hx)`. Establish `hN` using `Polynomial.hasDerivAt_aeval (numL (m + 1)) x`. Establish `hD` using `((hasDerivAt_id x).const_sub (1 : ℂ)).pow (m + 1)`. Establish `h` using `hN.div hD (pow_ne_zero (m + 1) hx')`. Use `⟨_, h, ?_⟩` and prove the remaining obligations.

Establish `e2 : numL (m + 2) = X * (derivative (numL (m + 1)) * (1 - X) + C ((m : ℤ) + 1) * numL (m + 1))`. Rewrite using `[numL.eq_3]`. Simplify using `only [Lk, e2, map_mul, map_add, map_sub, map_one, Polynomial.aeval_X, Polynomial.aeval_C, id, Nat.add_sub_cancel, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma lk_hasDerivAt (m : ℕ) (x : ℂ) (hx : x ≠ 1) :
    ∃ d : ℂ, HasDerivAt (fun w : ℂ => Lk (m + 1) w) d x ∧ x * d = Lk (m + 2) x := by
  have hx' : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hN := Polynomial.hasDerivAt_aeval (numL (m + 1)) x
  have hD := ((hasDerivAt_id x).const_sub (1 : ℂ)).pow (m + 1)
  have h := hN.div hD (pow_ne_zero (m + 1) hx')
  refine ⟨_, h, ?_⟩
  have e2 : numL (m + 2) = X * (derivative (numL (m + 1)) * (1 - X) + C ((m : ℤ) + 1) * numL (m + 1)) := by
    rw [numL.eq_3]
  simp only [Lk, e2, map_mul, map_add, map_sub, map_one, Polynomial.aeval_X, Polynomial.aeval_C,
    id, Nat.add_sub_cancel, Pi.pow_apply]
  field_simp
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `x hx`. Establish `h1 : x ≠ 1`. Introduce and unpack `rfl`.

Simplify using `at hx`. Establish `hg` using `(hasSum_geometric_of_norm_lt_one hx).mul_left x`. Establish `e : Lk 1 x = x * (1 - x)⁻¹`. Simplify using `[Lk, numL.eq_2, div_eq_mul_inv]`. Rewrite using `[e]`.

Establish `hf : (fun e : ℕ => ((e : ℂ) + 1) ^ 0 * x ^ (e + 1)) = fun i => x * x ^ i`. Use function extensionality and compare the values at `e`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Conclude with `hg`.

Consider the case `succ m ih`. Introduce `x hx`. Establish `h1 : x ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hx`.

Use `set r : ℝ := (‖x‖ + 1) / 2 with hr`. Establish `hr1 : r < 1` using `by rw [hr]; linarith`. Establish `hr0 : 0 < r` using `by rw [hr]; positivity`. Establish `hxr : ‖x‖ < r` using `by rw [hr]; linarith`. Establish `hrn : ‖r‖ < 1` using `by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1`.

Establish `hS : Summable (fun n : ℕ => (n : ℝ) ^ (m + 1) * r ^ n)` using `summable_pow_mul_geometric_of_norm_lt_one (m + 1) hrn`. Establish `hu : Summable (fun e : ℕ => ((e : ℝ) + 1) ^ (m + 1) * r ^ e)`. Establish `h2` using `((summable_nat_add_iff 1).mpr hS).mul_left r⁻¹`. Use `h2.congr (fun e => ?_)` and prove the remaining obligations. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Set `g : ℕ → ℂ → ℂ` to `fun e y => ((e : ℂ) + 1) ^ m * y ^ (e + 1)`. Set `g' : ℕ → ℂ → ℂ` to `fun e y => ((e : ℂ) + 1) ^ m * (((e + 1 : ℕ) : ℂ) * y ^ (e + 1 - 1))`. Establish `hgd : ∀ (e : ℕ), ∀ y ∈ Metric.ball (0 : ℂ) r, HasDerivAt (g e) (g' e y) y`.

Introduce `e y _`. Conclude with `(hasDerivAt_pow (e + 1) y).const_mul _`. Establish `hbd : ∀ (e : ℕ), ∀ y ∈ Metric.ball (0 : ℂ) r, ‖g' e y‖ ≤ ((e : ℝ) + 1) ^ (m + 1) * r ^ e`. Introduce `e y hy`. Rewrite `hy` using `[Metric.mem_ball, dist_zero_right]`.

Simplify using `only [g', Nat.add_sub_cancel, norm_mul, norm_pow]`. Establish `ha : ‖((e : ℂ) + 1)‖ = (e : ℝ) + 1`. Establish `: ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb : ‖(((e + 1 : ℕ) : ℂ))‖ = (e : ℝ) + 1`. Rewrite using `[Complex.norm_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ha, hb]`. Establish `hy' : ‖y‖ ^ e ≤ r ^ e` using `pow_le_pow_left₀ (norm_nonneg _) hy.le e`. Combine the equalities or inequalities in the displayed calculation. Establish `hxb : x ∈ Metric.ball (0 : ℂ) r`. Rewrite using `[Metric.mem_ball, dist_zero_right]`.

Conclude with `hxr`. Establish `hD` using `hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected hgd hbd hxb (ih x hx).summable hxb`. Establish `heq : (fun z => Lk (m + 1) z) =ᶠ[𝓝 x] (fun z => ∑' e, g e z)` using `by filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with z hz`. Rewrite `hz` using `[Metric.mem_ball, dist_zero_right]`. Conclude with `((ih z (by linarith)).tsum_eq).symm`.

Establish `hD2` using `hD.congr_of_eventuallyEq heq`. Take `⟨d, hd, hxd⟩` from `lk_hasDerivAt m x h1`. Establish `hdd : d = ∑' e, g' e x` using `hd.unique hD2`. Establish `hsum : Summable (fun e => g' e x)` using `Summable.of_norm_bounded hu (fun e => hbd e x hxb)`. Establish `hfin` using `hsum.hasSum.mul_left x`.

Rewrite `hfin` using `[← hdd, hxd]`. Establish `hf : (fun e : ℕ => ((e : ℂ) + 1) ^ (m + 1) * x ^ (e + 1)) = fun i => x * g' i x`. Use function extensionality and compare the values at `e`. Simplify using `only [g', Nat.add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Conclude with `hfin`.
-/
private lemma lk_hasSum_succ (m : ℕ) : ∀ x : ℂ, ‖x‖ < 1 →
    HasSum (fun e : ℕ => ((e : ℂ) + 1) ^ m * x ^ (e + 1)) (Lk (m + 1) x) := by
  induction m with
  | zero =>
    intro x hx
    have h1 : x ≠ 1 := by
      rintro rfl
      simp at hx
    have hg := (hasSum_geometric_of_norm_lt_one hx).mul_left x
    have e : Lk 1 x = x * (1 - x)⁻¹ := by
      simp [Lk, numL.eq_2, div_eq_mul_inv]
    rw [e]
    have hf : (fun e : ℕ => ((e : ℂ) + 1) ^ 0 * x ^ (e + 1)) = fun i => x * x ^ i := by
      funext e
      ring
    rw [hf]
    exact hg
  | succ m ih =>
    intro x hx
    have h1 : x ≠ 1 := by
      rintro rfl
      simp at hx
    set r : ℝ := (‖x‖ + 1) / 2 with hr
    have hr1 : r < 1 := by rw [hr]; linarith
    have hr0 : 0 < r := by rw [hr]; positivity
    have hxr : ‖x‖ < r := by rw [hr]; linarith
    have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
    have hS : Summable (fun n : ℕ => (n : ℝ) ^ (m + 1) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (m + 1) hrn
    have hu : Summable (fun e : ℕ => ((e : ℝ) + 1) ^ (m + 1) * r ^ e) := by
      have h2 := ((summable_nat_add_iff 1).mpr hS).mul_left r⁻¹
      refine h2.congr (fun e => ?_)
      push_cast
      field_simp
      ring
    let g : ℕ → ℂ → ℂ := fun e y => ((e : ℂ) + 1) ^ m * y ^ (e + 1)
    let g' : ℕ → ℂ → ℂ := fun e y => ((e : ℂ) + 1) ^ m * (((e + 1 : ℕ) : ℂ) * y ^ (e + 1 - 1))
    have hgd : ∀ (e : ℕ), ∀ y ∈ Metric.ball (0 : ℂ) r, HasDerivAt (g e) (g' e y) y := by
      intro e y _
      exact (hasDerivAt_pow (e + 1) y).const_mul _
    have hbd : ∀ (e : ℕ), ∀ y ∈ Metric.ball (0 : ℂ) r, ‖g' e y‖ ≤ ((e : ℝ) + 1) ^ (m + 1) * r ^ e := by
      intro e y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      simp only [g', Nat.add_sub_cancel, norm_mul, norm_pow]
      have ha : ‖((e : ℂ) + 1)‖ = (e : ℝ) + 1 := by
        have : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_natCast]
        push_cast
        ring
      have hb : ‖(((e + 1 : ℕ) : ℂ))‖ = (e : ℝ) + 1 := by
        rw [Complex.norm_natCast]
        push_cast
        ring
      rw [ha, hb]
      have hy' : ‖y‖ ^ e ≤ r ^ e := pow_le_pow_left₀ (norm_nonneg _) hy.le e
      calc ((e : ℝ) + 1) ^ m * (((e : ℝ) + 1) * ‖y‖ ^ e)
          ≤ ((e : ℝ) + 1) ^ m * (((e : ℝ) + 1) * r ^ e) := by gcongr
        _ = ((e : ℝ) + 1) ^ (m + 1) * r ^ e := by ring
    have hxb : x ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hxr
    have hD := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
      hgd hbd hxb (ih x hx).summable hxb
    have heq : (fun z => Lk (m + 1) z) =ᶠ[𝓝 x] (fun z => ∑' e, g e z) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact ((ih z (by linarith)).tsum_eq).symm
    have hD2 := hD.congr_of_eventuallyEq heq
    obtain ⟨d, hd, hxd⟩ := lk_hasDerivAt m x h1
    have hdd : d = ∑' e, g' e x := hd.unique hD2
    have hsum : Summable (fun e => g' e x) :=
      Summable.of_norm_bounded hu (fun e => hbd e x hxb)
    have hfin := hsum.hasSum.mul_left x
    rw [← hdd, hxd] at hfin
    have hf : (fun e : ℕ => ((e : ℂ) + 1) ^ (m + 1) * x ^ (e + 1)) = fun i => x * g' i x := by
      funext e
      simp only [g', Nat.add_sub_cancel]
      push_cast
      ring
    rw [hf]
    exact hfin

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 2` from `⟨k - 2, by omega⟩`. Establish `hk1 : m + 2 - 1 = m + 1` using `by omega`. Rewrite using `[hk1]`. Apply `(hasSum_nat_add_iff' 1).mp` to reduce the goal to its premises. Establish `h` using `lk_hasSum_succ (m + 1) x hx`.

Simplify using `only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_mul, sub_zero, Nat.cast_add, Nat.cast_one]`. Conclude with `h`.
-/
private lemma lk_hasSum (k : ℕ) (hk : 2 ≤ k) (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun e : ℕ => (e : ℂ) ^ (k - 1) * x ^ e) (Lk k x) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hk1 : m + 2 - 1 = m + 1 := by omega
  rw [hk1]
  apply (hasSum_nat_add_iff' 1).mp
  have h := lk_hasSum_succ (m + 1) x hx
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_mul, sub_zero, Nat.cast_add, Nat.cast_one]
  exact h

/- English proof (translation)
Establish `h` using `EisensteinSeries.linear_right_summable t 1 (k := (k : ℤ)) (by exact_mod_cast hk)`. Use `h.congr (fun j => ?_)` and prove the remaining obligations. Simplify using `[zpow_neg]`.
-/
private lemma lip_summable (k : ℕ) (hk : 2 ≤ k) (t : ℂ) : Summable (fun j : ℤ => (t + j) ^ (-(k : ℤ))) := by
  have h := EisensteinSeries.linear_right_summable t 1 (k := (k : ℤ)) (by exact_mod_cast hk)
  refine h.congr (fun j => ?_)
  simp [zpow_neg]

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 2` from `⟨k - 2, by omega⟩`. Use `set z : UpperHalfPlane := ⟨t, ht⟩ with hzdef`. Establish `hz : (z : ℂ) = t` using `rfl`. Establish `hq` using `EisensteinSeries.qExpansion_identity (k := m + 1) (by omega) z`. Rewrite `hq` using `[hz]`.

Establish `hs` using `(lk_hasSum (m + 2) hk _ (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).tsum_eq`. Rewrite `hs` using `[hz]`. Establish `hk1 : m + 2 - 1 = m + 1` using `by omega`. Rewrite `hs` using `[hk1]`. Establish `hj : ∀ j : ℤ, (t + j) ^ (-((m + 2 : ℕ) : ℤ)) = 1 / (t + j) ^ (m + 1 + 1)`.

Introduce `j`. Rewrite using `[zpow_neg, zpow_natCast, one_div]`. Repeatedly rewrite using `[hj]`. Rewrite using `[hq, lipC, ← hs, hk1]`.
-/
private lemma lip_pos (k : ℕ) (hk : 2 ≤ k) (t : ℂ) (ht : 0 < t.im) :
    ∑' j : ℤ, (t + j) ^ (-(k : ℤ)) = lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * t)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set z : UpperHalfPlane := ⟨t, ht⟩ with hzdef
  have hz : (z : ℂ) = t := rfl
  have hq := EisensteinSeries.qExpansion_identity (k := m + 1) (by omega) z
  rw [hz] at hq
  have hs := (lk_hasSum (m + 2) hk _ (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).tsum_eq
  rw [hz] at hs
  have hk1 : m + 2 - 1 = m + 1 := by omega
  rw [hk1] at hs
  have hj : ∀ j : ℤ, (t + j) ^ (-((m + 2 : ℕ) : ℤ)) = 1 / (t + j) ^ (m + 1 + 1) := by
    intro j
    rw [zpow_neg, zpow_natCast, one_div]
  simp_rw [hj]
  rw [hq, lipC, ← hs, hk1]

/- English proof (translation)
Establish `hne : ∀ j : ℤ, t + j ≠ 0`. Introduce `j h`. Apply `hj (-j)` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `h`.

Set `L : ℝ → ℂ` to `fun s => ∑' j : ℤ, (t + s * Complex.I + j) ^ (-(k : ℤ))`. Set `R : ℝ → ℂ` to `fun s => lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * (t + s * Complex.I)))`. Establish `hbound : Summable (fun j : ℤ => ‖(t + j) ^ (-(k : ℤ))‖)` using `summable_norm_iff.mpr (lip_summable k hk t)`. Establish `hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (∑' j : ℤ, (t + j) ^ (-(k : ℤ))))`. Apply `tendsto_tsum_of_dominated_convergence hbound` to reduce the goal to its premises.

Introduce `j`. Establish `hc : ContinuousAt (fun s : ℝ => (t + s * Complex.I + j) ^ (-(k : ℤ))) 0`. Apply `ContinuousAt.zpow₀ (by fun_prop)` to reduce the goal to its premises. Use `left`. Simplify using `using hne j`.

Use `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))` as an intermediate fact. Simplify using `using this`. Apply `Filter.Eventually.of_forall` to reduce the goal to its premises. Introduce `s j`. Establish `h0 : 0 < ‖t + j‖` using `norm_pos_iff.mpr (hne j)`.

Establish `hle : ‖t + j‖ ≤ ‖t + s * Complex.I + j‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_zpow, norm_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]`. Conclude with `inv_anti₀ (pow_pos h0 k) (pow_le_pow_left₀ h0.le hle k)`. Establish `hq1 : Complex.exp (2 * Real.pi * Complex.I * t) ≠ 1`.

Introduce `h`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp h`. Apply `hj n` to reduce the goal to its premises. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`.

Apply `mul_left_cancel₀ hpi` to reduce the goal to its premises. Take the linear combination `hn`. Establish `hR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * t))))`. Establish `hcL : ContinuousAt (fun w : ℂ => Lk k w) (Complex.exp (2 * Real.pi * Complex.I * t))` using `by show ContinuousAt (fun w : ℂ => Polynomial.aeval w (numL k) / (1 - w) ^ k) _`. Apply `ContinuousAt.div ((Polynomial.continuous_aeval (numL k)).continuousAt) (by fun_prop)` to reduce the goal to its premises.

Conclude with `pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hq1))`. Establish `he : ContinuousAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t + s * Complex.I))) 0` using `by fun_prop`. Establish `hc : ContinuousAt R 0`. Apply `ContinuousAt.mul continuousAt_const` to reduce the goal to its premises. Apply `ContinuousAt.comp (g := fun w : ℂ => Lk k w) _ he` to reduce the goal to its premises.

Simplify using `using hcL`. Use `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))` as an intermediate fact. Simplify `this` using `[R]`. Establish `heq : R =ᶠ[𝓝[>] (0 : ℝ)] L`. Apply `eventually_nhdsWithin_of_forall` to reduce the goal to its premises.

Introduce `s hs`. Establish `hs' : (0 : ℝ) < s` using `hs`. Establish `him : 0 < (t + s * Complex.I).im` using `by simp [ht, hs']`. Conclude with `(lip_pos k hk (t + s * Complex.I) him).symm`. Conclude with `tendsto_nhds_unique hL (hR.congr' heq)`.
-/
private lemma lip_real (k : ℕ) (hk : 2 ≤ k) (t : ℂ) (ht : t.im = 0) (hj : ∀ j : ℤ, t ≠ j) :
    ∑' j : ℤ, (t + j) ^ (-(k : ℤ)) = lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * t)) := by
  have hne : ∀ j : ℤ, t + j ≠ 0 := by
    intro j h
    apply hj (-j)
    push_cast
    linear_combination h
  let L : ℝ → ℂ := fun s => ∑' j : ℤ, (t + s * Complex.I + j) ^ (-(k : ℤ))
  let R : ℝ → ℂ := fun s => lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * (t + s * Complex.I)))
  have hbound : Summable (fun j : ℤ => ‖(t + j) ^ (-(k : ℤ))‖) :=
    summable_norm_iff.mpr (lip_summable k hk t)
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (∑' j : ℤ, (t + j) ^ (-(k : ℤ)))) := by
    apply tendsto_tsum_of_dominated_convergence hbound
    · intro j
      have hc : ContinuousAt (fun s : ℝ => (t + s * Complex.I + j) ^ (-(k : ℤ))) 0 := by
        apply ContinuousAt.zpow₀ (by fun_prop)
        left
        simpa using hne j
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    · apply Filter.Eventually.of_forall
      intro s j
      have h0 : 0 < ‖t + j‖ := norm_pos_iff.mpr (hne j)
      have hle : ‖t + j‖ ≤ ‖t + s * Complex.I + j‖ := by
        calc ‖t + j‖ ≤ |(t + j).re| + |(t + j).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |(t + s * Complex.I + j).re| := by simp [ht]
          _ ≤ ‖t + s * Complex.I + j‖ := Complex.abs_re_le_norm _
      rw [norm_zpow, norm_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos h0 k) (pow_le_pow_left₀ h0.le hle k)
  have hq1 : Complex.exp (2 * Real.pi * Complex.I * t) ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    apply hj n
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have hR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (lipC k * Lk k (Complex.exp (2 * Real.pi * Complex.I * t)))) := by
    have hcL : ContinuousAt (fun w : ℂ => Lk k w) (Complex.exp (2 * Real.pi * Complex.I * t)) := by
      show ContinuousAt (fun w : ℂ => Polynomial.aeval w (numL k) / (1 - w) ^ k) _
      apply ContinuousAt.div ((Polynomial.continuous_aeval (numL k)).continuousAt) (by fun_prop)
      exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hq1))
    have he : ContinuousAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t + s * Complex.I))) 0 := by
      fun_prop
    have hc : ContinuousAt R 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.comp (g := fun w : ℂ => Lk k w) _ he
      simpa using hcL
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [R] using this
  have heq : R =ᶠ[𝓝[>] (0 : ℝ)] L := by
    apply eventually_nhdsWithin_of_forall
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have him : 0 < (t + s * Complex.I).im := by simp [ht, hs']
    exact (lip_pos k hk (t + s * Complex.I) him).symm
  exact tendsto_nhds_unique hL (hR.congr' heq)

end UpperTheory.V.Sd

/- English proof (translation)
Introduce `k hk`. Use `⟨fun x hx => UpperTheory.V.Sd.lk_hasSum k hk x hx, fun t ht hj => ?_⟩` and prove the remaining obligations. Establish `hs` using `(UpperTheory.V.Sd.lip_summable k hk t).hasSum`. Break down `ht.lt_or_eq with h | h` into its components or cases. Rewrite `hs` using `[UpperTheory.V.Sd.lip_pos k hk t h]`. Then use the resulting hypothesis.

Rewrite `hs` using `[UpperTheory.V.Sd.lip_real k hk t h.symm hj]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Sd.lipschitz :
    UpperTheory.V.Sd.Lipschitz := by
  intro k hk
  refine ⟨fun x hx => UpperTheory.V.Sd.lk_hasSum k hk x hx, fun t ht hj => ?_⟩
  have hs := (UpperTheory.V.Sd.lip_summable k hk t).hasSum
  rcases ht.lt_or_eq with h | h
  · rwa [UpperTheory.V.Sd.lip_pos k hk t h] at hs
  · rwa [UpperTheory.V.Sd.lip_real k hk t h.symm hj] at hs
