import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete

noncomputable section

namespace PI.SSU

open Complex

/- English proof (translation)
Unfold `normF`. Establish `h1` using `hF (a * u)`. Establish `e1 : a * (u + 1) = a * u + a` using `by ring`. Rewrite using `[e1]`. Establish `hF' : F (a * u + a) = p * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) * (starRingEnd ℂ) a / A - (Real.pi : ℂ) * a * (starRingEnd ℂ) a / (2 * A)))`.

Rewrite using `[← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]`. Rewrite using `[hF', ← hl]`. Establish `key : ∀ (P e1 e2 e3 e4 : ℂ), e1 + e2 + e3 = e4 → Complex.exp e1 * P * Complex.exp e2 * Complex.exp e3 = P * Complex.exp e4`. Introduce `P e1 e2 e3 e4 h`. Rewrite using `[← h, Complex.exp_add, Complex.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Apply `key` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normF_one (a A l p : ℂ) (F : ℂ → ℂ) (hl : Complex.exp l = p) (hF : FE A a p F) (u : ℂ) :
    normF a A l F (u + 1) = normF a A l F u := by
  unfold normF
  have h1 := hF (a * u)
  have e1 : a * (u + 1) = a * u + a := by ring
  rw [e1]
  have hF' : F (a * u + a) = p * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) * (starRingEnd ℂ) a / A -
      (Real.pi : ℂ) * a * (starRingEnd ℂ) a / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF', ← hl]
  have key : ∀ (P e1 e2 e3 e4 : ℂ), e1 + e2 + e3 = e4 →
      Complex.exp e1 * P * Complex.exp e2 * Complex.exp e3 = P * Complex.exp e4 := by
    intro P e1 e2 e3 e4 h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  apply key
  ring

/- English proof (translation)
Unfold `normF`. Substitute `hτ` using the available equality. Establish `h1` using `hF (a * u)`. Establish `e1 : a * (u + τ) = a * u + a * τ` using `by ring`. Rewrite using `[e1]`.

Establish `hF' : F (a * u + a * τ) = q * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) * (starRingEnd ℂ) (a * τ) / A - (Real.pi : ℂ) * (a * τ) * (starRingEnd ℂ) (a * τ) / (2 * A)))`. Rewrite using `[← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]`. Rewrite using `[hF']`. Unfold `cst`. Establish `key : ∀ (qq P e1 e2 e3 e4 e5 : ℂ), e1 + e2 = e3 + e4 + e5 → qq * P * Complex.exp e1 * Complex.exp e2 = qq * Complex.exp e3 * Complex.exp e4 * (P * Complex.exp e5)`.

Introduce `qq P e1 e2 e3 e4 e5 h`. Establish `h2 : Complex.exp e1 * Complex.exp e2 = Complex.exp e3 * Complex.exp e4 * Complex.exp e5`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]`. Take the linear combination `(qq * P) * h2`. Apply `key` to reduce the goal to its premises.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normF_tau (a b τ A l q : ℂ) (F : ℂ → ℂ) (hτ : a * τ = b) (hF : FE A b q F) (u : ℂ) :
    normF a A l F (u + τ) = (q * Complex.exp (cst a b τ A l)) *
      Complex.exp ((Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) * u) *
      normF a A l F u := by
  unfold normF
  subst hτ
  have h1 := hF (a * u)
  have e1 : a * (u + τ) = a * u + a * τ := by ring
  rw [e1]
  have hF' : F (a * u + a * τ) = q * F (a * u) * Complex.exp (-(-(Real.pi : ℂ) * (a * u) *
      (starRingEnd ℂ) (a * τ) / A - (Real.pi : ℂ) * (a * τ) * (starRingEnd ℂ) (a * τ) / (2 * A))) := by
    rw [← h1, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hF']
  unfold cst
  have key : ∀ (qq P e1 e2 e3 e4 e5 : ℂ), e1 + e2 = e3 + e4 + e5 →
      qq * P * Complex.exp e1 * Complex.exp e2 = qq * Complex.exp e3 * Complex.exp e4 * (P * Complex.exp e5) := by
    intro qq P e1 e2 e3 e4 e5 h
    have h2 : Complex.exp e1 * Complex.exp e2 = Complex.exp e3 * Complex.exp e4 * Complex.exp e5 := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination (qq * P) * h2
  apply key
  simp only [map_mul]
  ring

/- English proof (translation)
Unfold `normF`. Use `fun_prop`.
-/
theorem normF_diff (a A l : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (normF a A l F) := by
  unfold normF
  fun_prop

/- English proof (translation)
Unfold `coef`. Establish `hf' : IntervalIntegrable (fun x : ℝ => f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x))) MeasureTheory.volume 0 1`. Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Use `fun_prop`. Establish `hg' : IntervalIntegrable (fun x : ℝ => g x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x))) MeasureTheory.volume 0 1`.

Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Use `fun_prop`. Rewrite using `[← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hf'.const_mul α) (hg'.const_mul β)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_lin (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) (α β : ℂ) (n : ℤ) :
    coef (fun u => α * f u - β * g u) n = α * coef f n - β * coef g n := by
  unfold coef
  have hf' : IntervalIntegrable (fun x : ℝ => f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg' : IntervalIntegrable (fun x : ℝ => g x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hf'.const_mul α) (hg'.const_mul β)]
  congr 1
  funext x
  ring

/- English proof (translation)
Establish `hl : Complex.exp (Complex.log p) = p` using `Complex.exp_log hp`. Establish `hτ : a * (b / a) = b` using `by field_simp`. Establish `hN` using `hK (normF a A (Complex.log p) F) (b / a) (q * Complex.exp (cst a b (b / a) A (Complex.log p))) k (normF_diff _ _ _ F hF) (mul_ne_zero hq (Complex.exp_ne_zero _)) hk1 (normF_one a A _ p F hl hFa) (fun u => by`. Rewrite using `[normF_tau a b (b / a) A _ q F hτ hFb u, hk]`. Use `congr 2`.

Use the proof step `ring_nf) h0`. Use function extensionality and compare the values at `z`. Use `congrFun hN (z / a)` as an intermediate fact. Simplify using `only [normF, Pi.zero_apply, mul_div_cancel₀ z ha, mul_eq_zero, Complex.exp_ne_zero, or_false] at this`. Simplify using `using this`.
-/
theorem zero_of_coef (hK : KeyP) (a b A p q : ℂ) (k : ℤ) (ha : a ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hk1 : k = 1 ∨ k = -1)
    (hk : (Real.pi : ℂ) / A * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * (Real.pi : ℂ) * I * k))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hFa : FE A a p F) (hFb : FE A b q F)
    (h0 : coef (normF a A (Complex.log p) F) 0 = 0) : F = 0 := by
  have hl : Complex.exp (Complex.log p) = p := Complex.exp_log hp
  have hτ : a * (b / a) = b := by field_simp
  have hN := hK (normF a A (Complex.log p) F) (b / a) (q * Complex.exp (cst a b (b / a) A (Complex.log p))) k
    (normF_diff _ _ _ F hF) (mul_ne_zero hq (Complex.exp_ne_zero _)) hk1
    (normF_one a A _ p F hl hFa)
    (fun u => by
      rw [normF_tau a b (b / a) A _ q F hτ hFb u, hk]
      congr 2; ring_nf) h0
  funext z
  have := congrFun hN (z / a)
  simp only [normF, Pi.zero_apply, mul_div_cancel₀ z ha, mul_eq_zero, Complex.exp_ne_zero, or_false]
    at this
  simpa using this

open Classical in
/- English proof (translation)
Introduce `a b hs G G' hG hG'`. Establish `harea : area (lat2 a b) = |((starRingEnd ℂ) a * b).im|` using `(hA a b hs).1`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at hs`. Establish `hma : a ∈ lat2 a b` using `AddSubgroup.subset_closure (by simp)`. Establish `hmb : b ∈ lat2 a b` using `AddSubgroup.subset_closure (by simp)`.

Apply the tactic sequence `have hp0 : (if a / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Apply the tactic sequence `have hq0 : (if b / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Establish `hz : a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b = -(2 * I * ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ))`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk1, hk⟩ : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ (Real.pi : ℂ) / ((area (lat2 a b) : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) = -(2 * (Real.pi : ℂ) * I * k) := by`.

Rewrite using `[harea, hz]`. Establish `hs' : ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hs`. Break down `lt_or_gt_of_ne hs with hneg | hpos` into its components or cases. Use `⟨-1, Or.inr rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_of_neg hneg]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `⟨1, Or.inl rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_of_pos hpos]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `FE_of : ∀ F : ℂ → ℂ, (∀ ω ∈ lat2 a b, ∀ z, U1 (lat2 a b) ω F z = (if ω / 2 ∈ lat2 a b then 1 else -1) * F z) → FE ((area (lat2 a b) : ℝ) : ℂ) a (if a / 2 ∈ lat2 a b then 1 else -1) F ∧ FE ((area (lat2 a b) : ℝ) : ℂ) b (if b / 2 ∈ lat2 a b then 1 else -1) F` using `fun F h => ⟨fun z => h a hma z, fun z => h b hmb z⟩`. Take `⟨hGa, hGb⟩` from `FE_of G hG.2.2.2`. Take `⟨hG'a, hG'b⟩` from `FE_of G' hG'.2.2.2`. Establish `Z` using `zero_of_coef hK a b _ _ _ k ha0 hp0 hq0 hk1 hk`.

Use `set c : (ℂ → ℂ) → ℂ := fun F => coef (normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) F) 0 with hc`. Establish `hH` using `Z (fun z => c G * G' z - c G' * G z) (by have := hG.1; have := hG'.1; fun_prop) (fun z => by linear_combination c G * hG'a z - c G' * hGa z) (fun z => by linear_combination c G * hG'b z - c G' * hGb z) (by`. Establish `e : normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) (fun z => c G * G' z - c G' * G z) = fun u => c G * normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G' u - c G' * normF a ((area (lat2 a b) : ℝ) : ℂ) …`. Use function extensionality and compare the values at `u`. Simplify using `only [normF]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, coef_lin _ _ (normF_diff _ _ _ _ hG'.1).continuous (normF_diff _ _ _ _ hG.1).continuous]`. Simplify using `only [hc]`. Use the proof step `ring)`. Establish `e : (fun z => c G * G' z) = (fun z => c G' * G z)`.

Use function extensionality and compare the values at `fun z => sub_eq_zero.1 (congrFun hH z)`. Establish `hd` using `congrArg (fun F => deriv F 0) e`. Rewrite `hd` using `[deriv_const_mul _ (hG'.1 0), deriv_const_mul _ (hG.1 0), hG.2.1, hG'.2.1]`. Distinguish the cases in `h0 : c G = 0`. It suffices to derive a contradiction.

Establish `hG0` using `Z G hG.1 hGa hGb h0`. Use `hG.2.1` as an intermediate fact. Rewrite `this` using `[hG0]`. Simplify using `at this`. Use function extensionality and compare the values at `z`.

Use `congrFun e z` as an intermediate fact. Simplify using `only [mul_one] at hd`. Rewrite `this` using `[← hd]`. Conclude with `(mul_left_cancel₀ h0 this).symm`.
-/
theorem main_of (hK : KeyP) (hA : AreaLat) : SigmaStarUniq := by
  intro a b hs G G' hG hG'
  have harea : area (lat2 a b) = |((starRingEnd ℂ) a * b).im| := (hA a b hs).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at hs
  have hma : a ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hmb : b ∈ lat2 a b := AddSubgroup.subset_closure (by simp)
  have hp0 : (if a / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hq0 : (if b / 2 ∈ lat2 a b then (1:ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hz : a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b =
      -(2 * I * ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp <;> ring
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      (Real.pi : ℂ) / ((area (lat2 a b) : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
        -(2 * (Real.pi : ℂ) * I * k) := by
    rw [harea, hz]
    have hs' : ((((starRingEnd ℂ) a * b).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_neg hneg]; push_cast; field_simp
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_pos hpos]; push_cast; field_simp
  have FE_of : ∀ F : ℂ → ℂ, (∀ ω ∈ lat2 a b, ∀ z, U1 (lat2 a b) ω F z =
      (if ω / 2 ∈ lat2 a b then 1 else -1) * F z) →
      FE ((area (lat2 a b) : ℝ) : ℂ) a (if a / 2 ∈ lat2 a b then 1 else -1) F ∧
      FE ((area (lat2 a b) : ℝ) : ℂ) b (if b / 2 ∈ lat2 a b then 1 else -1) F :=
    fun F h => ⟨fun z => h a hma z, fun z => h b hmb z⟩
  obtain ⟨hGa, hGb⟩ := FE_of G hG.2.2.2
  obtain ⟨hG'a, hG'b⟩ := FE_of G' hG'.2.2.2
  have Z := zero_of_coef hK a b _ _ _ k ha0 hp0 hq0 hk1 hk
  set c : (ℂ → ℂ) → ℂ := fun F => coef (normF a ((area (lat2 a b) : ℝ) : ℂ)
    (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) F) 0 with hc
  have hH := Z (fun z => c G * G' z - c G' * G z) (by have := hG.1; have := hG'.1; fun_prop)
    (fun z => by linear_combination c G * hG'a z - c G' * hGa z)
    (fun z => by linear_combination c G * hG'b z - c G' * hGb z)
    (by
      have e : normF a ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1))
          (fun z => c G * G' z - c G' * G z) = fun u => c G * normF a ((area (lat2 a b) : ℝ) : ℂ)
            (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G' u - c G' * normF a
            ((area (lat2 a b) : ℝ) : ℂ) (Complex.log (if a / 2 ∈ lat2 a b then 1 else -1)) G u := by
        funext u; simp only [normF]; ring
      rw [e, coef_lin _ _ (normF_diff _ _ _ _ hG'.1).continuous (normF_diff _ _ _ _ hG.1).continuous]
      simp only [hc]; ring)
  have e : (fun z => c G * G' z) = (fun z => c G' * G z) :=
    funext fun z => sub_eq_zero.1 (congrFun hH z)
  have hd := congrArg (fun F => deriv F 0) e
  rw [deriv_const_mul _ (hG'.1 0), deriv_const_mul _ (hG.1 0), hG.2.1, hG'.2.1] at hd
  by_cases h0 : c G = 0
  · exfalso
    have hG0 := Z G hG.1 hGa hGb h0
    have := hG.2.1
    rw [hG0] at this
    simp at this
  · funext z
    have := congrFun e z
    simp only [mul_one] at hd
    rw [← hd] at this
    exact (mul_left_cancel₀ h0 this).symm

end PI.SSU
