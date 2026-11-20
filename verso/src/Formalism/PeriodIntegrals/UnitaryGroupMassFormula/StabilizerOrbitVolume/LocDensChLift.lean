import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar

noncomputable section

open NumberField Complex

namespace PI.VolStabSW

namespace ChLiftW

/- English proof (translation)
Take `⟨n, hn⟩` from `hint p`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[hn]`. Establish `hn0 : n ≠ 0` using `by exact_mod_cast hne`. Break down `lt_or_gt_of_ne hn0 with hlt | hgt` into its components or cases.

Establish `hiv` using `isPreconnected_univ.intermediate_value (Set.mem_univ p) (Set.mem_univ a) hψ.continuousOn`. Establish `hle : (n : ℝ) ≤ -1`. Establish `h' : n ≤ -1` using `by omega`. Conclude with `h'` after adjusting the coercions. Establish `hm : (-1 / 2 : ℝ) ∈ Set.Icc (ψ p) (ψ a)`.

Apply the tactic sequence `rw [hn, ha]; constructor <;> linarith`. Take `⟨q, -, hq⟩` from `hiv hm`. Take `⟨m, hm'⟩` from `hint q`. Rewrite `hq` using `[hm']`. Establish `h2 : ((2 * m : ℤ) : ℝ) = -1` using `by push_cast; linarith`.

Establish `h3 : 2 * m = -1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `hiv` using `isPreconnected_univ.intermediate_value (Set.mem_univ a) (Set.mem_univ p) hψ.continuousOn`. Establish `hle : (1 : ℝ) ≤ n`. Establish `h' : 1 ≤ n` using `by omega`.

Conclude with `h'` after adjusting the coercions. Establish `hm : (1 / 2 : ℝ) ∈ Set.Icc (ψ a) (ψ p)`. Apply the tactic sequence `rw [hn, ha]; constructor <;> linarith`. Take `⟨q, -, hq⟩` from `hiv hm`. Take `⟨m, hm'⟩` from `hint q`.

Rewrite `hq` using `[hm']`. Establish `h2 : ((2 * m : ℤ) : ℝ) = 1` using `by push_cast; linarith`. Establish `h3 : 2 * m = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  by_contra hne
  rw [hn] at hne
  have hn0 : n ≠ 0 := by exact_mod_cast hne
  rcases lt_or_gt_of_ne hn0 with hlt | hgt
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ p) (Set.mem_univ a) hψ.continuousOn
    have hle : (n : ℝ) ≤ -1 := by
      have h' : n ≤ -1 := by omega
      exact_mod_cast h'
    have hm : (-1 / 2 : ℝ) ∈ Set.Icc (ψ p) (ψ a) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ a) (Set.mem_univ p) hψ.continuousOn
    have hle : (1 : ℝ) ≤ n := by
      have h' : 1 ≤ n := by omega
      exact_mod_cast h'
    have hm : (1 / 2 : ℝ) ∈ Set.Icc (ψ a) (ψ p) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

/- English proof (translation)
Establish `hne : ∀ x, χ x ≠ 0`. Introduce `x h`. Establish `h1` using `hadd x (-x)`. Rewrite `h1` using `[add_neg_cancel, h0, h, zero_mul]`. Conclude with `one_ne_zero h1`.

Establish `hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k`. Introduce `k y`. Proceed by induction on `k with`. Consider the case `zero => simp [h0]`. Consider the case `succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]`.

Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by`. Take `⟨ε, hε, h⟩` from `Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)`. Use `⟨ε / 2, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h2` using `h (x := y) (by rw [dist_zero_right]; linarith)`. Rewrite `h2` using `[h0, dist_eq_norm]`. Then use the resulting hypothesis.

Establish `hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re`. Introduce `y hy`. Establish `h1` using `hball y hy`. Establish `h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖` using `Complex.abs_re_le_norm _`. Rewrite `h2` using `[Complex.sub_re, Complex.one_re]`.

Establish `h3` using `(abs_le.1 (h2.trans h1.le)).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2` using `fun y hy => Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))`. Use `set L : W → ℂ := fun y => Complex.log (χ y) with hL`. Establish `hL0 : L 0 = 0` using `by simp [hL, h0]`.

Establish `hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z`. Introduce `y z hy hz`. Simplify using `only [hL]`. Establish `h1` using `abs_lt.1 (harg y hy)`. Establish `h2` using `abs_lt.1 (harg z hz)`.

Rewrite using `[hadd, Complex.log_mul (hne y) (hne z)]`. Apply the tactic sequence `constructor <;> linarith [Real.pi_pos]`. Establish `hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y`. Introduce `k y`. Proceed by induction on `k with`.

Consider the case `zero => intro _`. Simplify using `[hL0]`. Consider the case `succ k ih`. Introduce `hk`. Establish `hy0` using `norm_nonneg y`.

Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Move the coercions through the operations in `at hk`. Establish `h1 : (k : ℝ) * ‖y‖ ≤ δ` using `by nlinarith`. Establish `h2 : ‖y‖ ≤ δ` using `by nlinarith`. Establish `h3 : ‖(k : ℝ) • y‖ ≤ δ` using `by rw [norm_smul, Real.norm_natCast]; exact h1`.

Rewrite using `[Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ → (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x)`. Introduce `a b x ha hb hxa hxb`.

Establish `ha' : (0 : ℝ) < a` using `Nat.cast_pos.2 ha`. Establish `hb' : (0 : ℝ) < b` using `Nat.cast_pos.2 hb`. Establish `e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x`. Rewrite using `[smul_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Establish `e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x`. Rewrite using `[smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b)`. Rewrite using `[norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ`. Rewrite using `[ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ`. Rewrite using `[ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]`.

Expand and normalize the polynomial expressions, which then agree. Use `set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN`. Establish `hNpos : ∀ x, 0 < N x` using `fun x => Nat.succ_pos _`. Establish `hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ`. Introduce `x`.

Establish `h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊` using `Nat.le_ceil _`. Establish `h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ` using `by rwa [div_le_iff₀ hδ] at h1`. Simplify using `only [hN]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Use `set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf`. Establish `hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x)` using `fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx`. Establish `hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ`. Introduce `M x hM hx`. Establish `hM' : (0 : ℝ) < M` using `Nat.cast_pos.2 hM`.

Rewrite using `[norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `fadd : ∀ x y, f (x + y) = f x + f y`. Introduce `x y`. Establish `hMpos : 0 < N x + N y` using `by have := hNpos x; omega`.

Establish `hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ`. Apply `mul_le_mul_of_nonneg_right _ hδ.le` to reduce the goal to its premises. Conclude with `(by omega : N x ≤ N x + N y)` after adjusting the coercions. Establish `hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ`. Apply `mul_le_mul_of_nonneg_right _ hδ.le` to reduce the goal to its premises.

Conclude with `(by omega : N y ≤ N x + N y)` after adjusting the coercions. Establish `hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ` using `(hNle x).trans hcx`. Establish `hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ` using `(hNle y).trans hcy`. Establish `hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ`. Establish `h1` using `norm_add_le x y`.

Establish `h2` using `hNle x`. Establish `h3` using `hNle y`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add, hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]`.

Establish `fexp : ∀ x, χ x = Complex.exp (f x)`. Introduce `x`. Use `show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))`. Rewrite using `[Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul, mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]`. Establish `fcont : Continuous f`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Establish `hMpos : 0 < N x0 + 1` using `Nat.succ_pos _`. Establish `hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1` using `by push_cast; ring`. Establish `hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ`.

Rewrite using `[hMr]`. Use polynomial arithmetic with `[hNle x0]`. Establish `heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f` using `by filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx`. Rewrite `hx` using `[Metric.mem_ball, dist_eq_norm]`. Establish `h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ`.

Establish `h2` using `norm_sub_norm_le x x0`. Rewrite using `[hMr]`. Use polynomial arithmetic with `[hNle x0]`. Conclude with `(hfM _ x hMpos h1).symm`. Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations.

Apply `ContinuousAt.mul continuousAt_const` to reduce the goal to its premises. Simplify using `only [hL]`. Apply `ContinuousAt.clog` to reduce the goal to its premises. Conclude with `(hc.comp (continuous_const_smul _)).continuousAt`. Conclude with `Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))`.

Conclude with `⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩`.
-/
theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := by
    intro x h
    have h1 := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k := by
    intro k y
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have h2 := h (x := y) (by rw [dist_zero_right]; linarith)
    rwa [h0, dist_eq_norm] at h2
  have hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re := by
    intro y hy
    have h1 := hball y hy
    have h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (h2.trans h1.le)).1
    linarith
  have harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2 := fun y hy =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))
  set L : W → ℂ := fun y => Complex.log (χ y) with hL
  have hL0 : L 0 = 0 := by simp [hL, h0]
  have hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z := by
    intro y z hy hz
    simp only [hL]
    have h1 := abs_lt.1 (harg y hy)
    have h2 := abs_lt.1 (harg z hz)
    rw [hadd, Complex.log_mul (hne y) (hne z)]
    constructor <;> linarith [Real.pi_pos]
  have hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y := by
    intro k y
    induction k with
    | zero => intro _; simp [hL0]
    | succ k ih =>
      intro hk
      have hy0 := norm_nonneg y
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      have h1 : (k : ℝ) * ‖y‖ ≤ δ := by nlinarith
      have h2 : ‖y‖ ≤ δ := by nlinarith
      have h3 : ‖(k : ℝ) • y‖ ≤ δ := by rw [norm_smul, Real.norm_natCast]; exact h1
      rw [Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]
      push_cast
      ring
  have hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ →
      (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x) := by
    intro a b x ha hb hxa hxb
    have ha' : (0 : ℝ) < a := Nat.cast_pos.2 ha
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      ring
    have hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']
      linarith
    have ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']
      linarith
    rw [← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]
    ring
  set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN
  have hNpos : ∀ x, 0 < N x := fun x => Nat.succ_pos _
  have hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ := by
    intro x
    have h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊ := Nat.le_ceil _
    have h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ := by rwa [div_le_iff₀ hδ] at h1
    simp only [hN]
    push_cast
    nlinarith
  set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf
  have hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x) :=
    fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx
  have hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ := by
    intro M x hM hx
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']
    linarith
  have fadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have hMpos : 0 < N x + N y := by have := hNpos x; omega
    have hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N x ≤ N x + N y)
    have hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N y ≤ N x + N y)
    have hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle x).trans hcx
    have hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle y).trans hcy
    have hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      have h1 := norm_add_le x y
      have h2 := hNle x
      have h3 := hNle y
      push_cast
      linarith
    rw [hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add,
      hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]
  have fexp : ∀ x, χ x = Complex.exp (f x) := by
    intro x
    show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))
    rw [Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]
  have fcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hMpos : 0 < N x0 + 1 := Nat.succ_pos _
    have hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1 := by push_cast; ring
    have hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
      rw [hMr]
      nlinarith [hNle x0]
    have heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f := by
      filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
        have h2 := norm_sub_norm_le x x0
        rw [hMr]
        nlinarith [hNle x0]
      exact (hfM _ x hMpos h1).symm
    refine ContinuousAt.congr ?_ heq
    apply ContinuousAt.mul continuousAt_const
    simp only [hL]
    apply ContinuousAt.clog
    · exact (hc.comp (continuous_const_smul _)).continuousAt
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))
  exact ⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩

/- English proof (translation)
Establish `he0 : e 0 = 0` using `by simpa using he 0 0`. Establish `hs0 : e.symm 0 = 0` using `by rw [← he0, Homeomorph.symm_apply_apply]`. Establish `hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w'`. Introduce `w w'`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]`. Take `⟨ℓ', hℓc, hℓ⟩` from `lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous) (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])`. Use `⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add]), hℓc.comp e.continuous, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `hℓ (e x)`. Simplify using `only [Homeomorph.symm_apply_apply] at h1`.

Conclude with `h1`.
-/
theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1

/- English proof (translation)
Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Conclude with `lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0`. Conclude with `lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0`.
-/
theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0

/- English proof (translation)
Use `Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
/- English proof (translation)
The claim follows from `Pi.single_add v x y`.
-/
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
/- English proof (translation)
The claim follows from `Pi.single_zero v`.
-/
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
/- English proof (translation)
The claim follows from `continuous_single v`.
-/
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v

open Classical in
/- English proof (translation)
Simplify using `only [sgl]`. Conclude with `Finset.univ_sum_single x`.
-/
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x

open ChLiftW in
/- English proof (translation)
Introduce `F _ _ χ hχ`. Establish `key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ t, χ (sgl v t) = exp (ℓ t)`. Introduce `v`. Conclude with `lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v)) (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])`. Use `choose ℓ hℓc hℓ using key`.

Use `⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← map_add]`. Both sides reduce to the same expression.

Conclude with `continuous_finset_sum _ fun v _ => (hℓc v).comp (continuous_apply v)`. Use `show χ x = Complex.exp (∑ v, ℓ v (x v)) conv_lhs => rw [← sum_sgl x]`. Rewrite using `[ChLiftW.addChar_sum, Complex.exp_sum]`. Conclude with `Finset.prod_congr rfl fun v _ => hℓ v (x v)`.
-/
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := by
    intro v
    exact lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓ hℓc hℓ using key
  refine ⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_add]
    rfl
  · exact continuous_finset_sum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · show χ x = Complex.exp (∑ v, ℓ v (x v))
    conv_lhs => rw [← sum_sgl x]
    rw [ChLiftW.addChar_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabSW
