import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hre : ρ.re < 1`. Assume the negation of the conclusion as `h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ`. Establish `hz : ((σ : ℂ) - ρ).re = σ - ρ.re` using `by simp`. Establish `hpos : 0 < ((σ : ℂ) - ρ).re` using `by rw [hz]; linarith`.

Establish `hne : ((σ : ℂ) - ρ) ≠ 0`. Introduce `h`. Rewrite `hpos` using `[h]`. Simplify using `at hpos`. Rewrite using `[one_div, Complex.inv_re]`.

Conclude with `div_pos hpos (Complex.normSq_pos.mpr hne)`.
-/
lemma re_one_div_sub_zero_pos' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ
  have hz : ((σ : ℂ) - ρ).re = σ - ρ.re := by simp
  have hpos : 0 < ((σ : ℂ) - ρ).re := by rw [hz]; linarith
  have hne : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)

/- English proof (translation)
Rewrite using `[one_div, Complex.inv_re, Complex.normSq_apply]`. Simplify using `only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma re_one_div_ofReal_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/- English proof (translation)
Establish `hX : 0 < X`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hv : (T * G) ^ 2 ≤ 1 / 100`.

Use `sq_abs (T * G)` as an intermediate fact. Use polynomial arithmetic with `[abs_nonneg (T * G)]`. Establish `key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X`. Use polynomial arithmetic with `[mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]`. Use `le_of_mul_le_mul_left key hT` as an intermediate fact.

Rewrite using `[le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]`. Conclude with `this`.
-/
lemma mul_le_div_sq_add_sq (T X G : ℝ) (hT : 0 < T) (h1 : 1 ≤ T * X) (h2 : T * X ≤ 11 / 10)
    (h3 : |T * G| ≤ 1 / 10) : 4 / 5 * T ≤ X / (X ^ 2 + G ^ 2) := by
  have hX : 0 < X := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hv : (T * G) ^ 2 ≤ 1 / 100 := by
    have := sq_abs (T * G)
    nlinarith [abs_nonneg (T * G)]
  have key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]
  have := le_of_mul_le_mul_left key hT
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]
  exact this

/- English proof (translation)
Introduce `hLZ hLD hPos hConj`. Take `⟨C, hC⟩` from `hLZ`. Take `⟨C₀, hC₀, hLD⟩` from `hLD`. Use `set Cp : ℝ := max C 0 with hCp`. Establish `hCp0 : 0 ≤ Cp` using `le_max_right _ _`.

Establish `hCCp : C ≤ Cp` using `le_max_left _ _`. Use `set K : ℝ := 2 * C₀ + Cp with hK`. Establish `hK0 : 0 ≤ K` using `by rw [hK]; linarith`. Use `set W : ℝ := 10 * (K + 1) with hW`. Establish `hW10 : 10 ≤ W` using `by rw [hW]; linarith`.

Establish `hWpos : 0 < W` using `by linarith`. Use `⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ2 hχ`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Take `⟨Z, m, hZ, hm1, hm2, hb⟩` from `hC q χ hχ 0`.

Simplify using `only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb`. Use `set L₀ := Real.log ((q : ℝ) * 2) with hL₀`. Establish `hlog2` using `Real.log_two_gt_d9`. Establish `hL₀2 : Real.log 2 ≤ L₀` using `Real.log_le_log (by norm_num) (by nlinarith)`. Establish `hL₀h : 1 / 2 < L₀` using `by norm_num at hlog2; linarith`.

Establish `hL₀pos : 0 < L₀` using `by linarith`. Use `set T : ℝ := W * L₀ with hT`. Establish `hTpos : 0 < T` using `mul_pos hWpos hL₀pos`. Establish `hT5 : 5 ≤ T` using `by rw [hT]; nlinarith`. Establish `hTe : T = 10 * (K * L₀) + 10 * L₀` using `by rw [hT, hW]; ring`.

Establish `hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀` using `by rw [hK]; ring`. Use `set σ : ℝ := 1 + 1 / T with hσ`. Establish `hσ1 : 1 < σ`. Establish `: 0 < 1 / T` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hσ2 : σ ≤ 6 / 5`. Establish `: 1 / T ≤ 1 / 5` using `one_div_le_one_div_of_le (by norm_num) hT5`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀`. Establish `hP` using `(hPos q σ hσ1).2.1 χ hχ2`.

Establish `h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀`. Establish `h` using `hLD q 1 (σ : ℂ) (by simpa using hσ1)`. Establish `e : 1 / ((σ : ℂ).re - 1) = T`. Rewrite using `[Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]`. Rewrite `h` using `[e]`.

Conclude with `(Complex.re_le_norm _).trans h`. Establish `h1` using `hb σ hσ1 hσ2`. Establish `h2 : C * L₀ ≤ Cp * L₀` using `mul_le_mul_of_nonneg_right hCCp hL₀pos.le`. Establish `h3 : C₀ ≤ 2 * (C₀ * L₀)` using `by nlinarith`. Establish `h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀` using `by ring`.

Rewrite using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re` using `fun ρ hρ => mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le`. Establish `hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) → InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 → ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re`. Introduce `ρ hi hr hz`.

Unfold `InRegion at hr`. Take `⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2))` from `⟨_, rfl⟩`. Rewrite `hi`, `hr` using `[← hLρdef]`. Establish `hLρ : L₀ ≤ Lρ`. Rewrite using `[hLρdef, hL₀]`.

Conclude with `Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])`. Establish `hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T)`. Use `div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ` as an intermediate fact. Establish `e : 1 / (10 * W) / L₀ = 1 / (10 * T)` using `by rw [hT, div_div, mul_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hβ1 : ρ.re < 1`. Assume the negation of the conclusion as `h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz`. Establish `hβ : 1 - 1 / (10 * T) ≤ ρ.re` using `by linarith`. Establish `hγ : |ρ.im| ≤ 1 / (10 * T)` using `by linarith`.

Establish `hsmall : 1 / (10 * T) ≤ 1 / 50` using `one_div_le_one_div_of_le (by norm_num) (by linarith)`. Establish `hTT : T * (1 / (10 * T)) = 1 / 10` using `by field_simp`. Use `⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, Complex.dist_eq]`. Use `(Complex.norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations.

Establish `e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]`. Establish `: |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T)`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[re_one_div_ofReal_sub]`. Establish `hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1`. Rewrite using `[hσ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : 0 < T * (1 - ρ.re)` using `mul_pos hTpos (by linarith)`. Establish `hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T))` using `mul_le_mul_of_nonneg_left (by linarith) hTpos.le`. Apply `mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos` to reduce the goal to its premises. Rewrite using `[hTσ]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hTσ]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_mul, abs_of_pos hTpos]`. Use `mul_le_mul_of_nonneg_left hγ hTpos.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbig : (11 * K + 10) * L₀ < 8 / 5 * T`. Establish `: 0 ≤ K * L₀` using `mul_nonneg hK0 hL₀pos.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `htwo : ∀ ρ₁ ρ₂ : ℂ, (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧ InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) → (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧ InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ …`. Introduce and unpack `ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne`.

Take `⟨h1Z, h1r⟩` from `hcons ρ₁ a1 b1 c1`. Take `⟨h2Z, h2r⟩` from `hcons ρ₂ a2 b2 c2`. Establish `hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z`. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_insert, Finset.mem_singleton]`.

Break down `hx with rfl | rfl` into its components or cases. Conclude with `h1Z`. Conclude with `h2Z`. Establish `hs` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)`. Rewrite `hs` using `[Finset.sum_pair hne]`.

Establish `hm1' : (1 : ℝ) ≤ m ρ₁` using `by exact_mod_cast hm1 ρ₁ h1Z`. Establish `hm2' : (1 : ℝ) ≤ m ρ₂` using `by exact_mod_cast hm1 ρ₂ h2Z`. Establish `hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re` using `by linarith`. Establish `hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]`.

Establish `hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) → InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 → deriv (DirichletCharacter.LFunction χ) ρ = 0 → False`. Introduce `ρ a b c hd`. Take `⟨hρZ, hρr⟩` from `hcons ρ a b c`. Establish `hs` using `Finset.single_le_sum hnn hρZ`. Establish `hm : (2 : ℝ) ≤ m ρ` using `by exact_mod_cast hm2 ρ hρZ hd`.

Establish `hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hm) hr]`. Introduce `s s' hs hs' hrs hrs' hz hz'`. Establish `hsim : s.im = 0`. Assume the negation of the conclusion as `hne`.

Use `htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Simplify `hs` using `[Complex.conj_im, abs_neg]`. Unfold `InRegion at hrs ⊢`. Simplify `hrs` using `[Complex.conj_re, Complex.conj_im, abs_neg]`. Rewrite using `[hConj q χ hχ2 hχ s, hz, map_zero]`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Use `congrArg Complex.im h` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne`.
-/
theorem realCharZeroSmallHeightOfBounds : RealSmallTOf := by
  intro hLZ hLD hPos hConj
  obtain ⟨C, hC⟩ := hLZ
  obtain ⟨C₀, hC₀, hLD⟩ := hLD
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set K : ℝ := 2 * C₀ + Cp with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set W : ℝ := 10 * (K + 1) with hW
  have hW10 : 10 ≤ W := by rw [hW]; linarith
  have hWpos : 0 < W := by linarith
  refine ⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩
  intro q _ χ hχ2 hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

  obtain ⟨Z, m, hZ, hm1, hm2, hb⟩ := hC q χ hχ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb
  set L₀ := Real.log ((q : ℝ) * 2) with hL₀
  have hlog2 := Real.log_two_gt_d9
  have hL₀2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
  have hL₀h : 1 / 2 < L₀ := by norm_num at hlog2; linarith
  have hL₀pos : 0 < L₀ := by linarith
  set T : ℝ := W * L₀ with hT
  have hTpos : 0 < T := mul_pos hWpos hL₀pos
  have hT5 : 5 ≤ T := by rw [hT]; nlinarith
  have hTe : T = 10 * (K * L₀) + 10 * L₀ := by rw [hT, hW]; ring
  have hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀ := by rw [hK]; ring
  set σ : ℝ := 1 + 1 / T with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / T := by positivity
    linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : 1 / T ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hT5
    linarith

  have hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀ := by
    have hP := (hPos q σ hσ1).2.1 χ hχ2
    have h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀ := by
      have h := hLD q 1 (σ : ℂ) (by simpa using hσ1)
      have e : 1 / ((σ : ℂ).re - 1) = T := by
        rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]
      rw [e] at h
      exact (Complex.re_le_norm _).trans h
    have h1 := hb σ hσ1 hσ2
    have h2 : C * L₀ ≤ Cp * L₀ := mul_le_mul_of_nonneg_right hCCp hL₀pos.le
    have h3 : C₀ ≤ 2 * (C₀ * L₀) := by nlinarith
    have h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀ := by ring
    rw [h4]
    linarith

  have hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le

  have hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re := by
    intro ρ hi hr hz
    unfold InRegion at hr
    obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hLρdef] at hi hr
    have hLρ : L₀ ≤ Lρ := by
      rw [hLρdef, hL₀]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T) := by
      have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ
      have e : 1 / (10 * W) / L₀ = 1 / (10 * T) := by rw [hT, div_div, mul_assoc]
      linarith
    have hβ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz
    have hβ : 1 - 1 / (10 * T) ≤ ρ.re := by linarith
    have hγ : |ρ.im| ≤ 1 / (10 * T) := by linarith
    have hsmall : 1 / (10 * T) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hTT : T * (1 / (10 * T)) = 1 / 10 := by field_simp
    refine ⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by push_cast; rfl
      rw [e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      have : |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · rw [re_one_div_ofReal_sub]
      have hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1 := by
        rw [hσ]; field_simp; ring
      have hA : 0 < T * (1 - ρ.re) := mul_pos hTpos (by linarith)
      have hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T)) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      apply mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos
      · rw [hTσ]; linarith
      · rw [hTσ]; linarith
      · rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hγ hTpos.le
        linarith
  have hbig : (11 * K + 10) * L₀ < 8 / 5 * T := by
    have : 0 ≤ K * L₀ := mul_nonneg hK0 hL₀pos.le
    nlinarith

  have htwo : ∀ ρ₁ ρ₂ : ℂ,
      (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) →
      (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ ρ₂ = 0) →
      ρ₁ ≠ ρ₂ → False := by
    rintro ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne
    obtain ⟨h1Z, h1r⟩ := hcons ρ₁ a1 b1 c1
    obtain ⟨h2Z, h2r⟩ := hcons ρ₂ a2 b2 c2
    have hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1Z
      · exact h2Z
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)
    rw [Finset.sum_pair hne] at hs
    have hm1' : (1 : ℝ) ≤ m ρ₁ := by exact_mod_cast hm1 ρ₁ h1Z
    have hm2' : (1 : ℝ) ≤ m ρ₂ := by exact_mod_cast hm1 ρ₂ h2Z
    have hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re := by linarith
    have hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]

  have hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      deriv (DirichletCharacter.LFunction χ) ρ = 0 → False := by
    intro ρ a b c hd
    obtain ⟨hρZ, hρr⟩ := hcons ρ a b c
    have hs := Finset.single_le_sum hnn hρZ
    have hm : (2 : ℝ) ≤ m ρ := by exact_mod_cast hm2 ρ hρZ hd
    have hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hr]
  intro s s' hs hs' hrs hrs' hz hz'
  have hsim : s.im = 0 := by
    by_contra hne
    refine htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_
    · simpa [Complex.conj_im, abs_neg] using hs
    · unfold InRegion at hrs ⊢
      simpa [Complex.conj_re, Complex.conj_im, abs_neg] using hrs
    · rw [hConj q χ hχ2 hχ s, hz, map_zero]
    · intro h
      apply hne
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  refine ⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩
  by_contra hne
  exact htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne

end Formalism.ZeroFreeDirichlet
