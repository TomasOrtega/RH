import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

namespace GlobalTheory.CompanionTheory.RgEisDGood

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

/- English proof (translation)
Take `⟨B, hB⟩ : ∃ B : ℝ, B = max |b| |c|` from `⟨_, rfl⟩`. Establish `hbB : |b| ≤ B` using `hB ▸ le_max_left _ _`. Establish `hcB : |c| ≤ B` using `hB ▸ le_max_right _ _`. Establish `hB0 : 0 ≤ B` using `(abs_nonneg b).trans hbB`. Take `⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + B` from `⟨_, rfl⟩`.

Establish `hT : 1 ≤ T` using `by linarith`. Use `⟨16 * T ^ 4 * Real.exp (B ^ 2), by positivity, fun z h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨x, hxdef⟩ : ∃ x : ℝ, x = z.re` from `⟨_, rfl⟩`. Take `⟨y, hydef⟩ : ∃ y : ℝ, y = z.im` from `⟨_, rfl⟩`. Establish `hx : |x| ≤ B`.

Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Use `neg_abs_le b` as an intermediate fact. Rewrite using `[hxdef]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `le_abs_self c` as an intermediate fact. Rewrite using `[hxdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx2 : x ^ 2 ≤ B ^ 2`. Use `pow_le_pow_left₀ (abs_nonneg x) hx 2` as an intermediate fact.

Rewrite `this` using `[sq_abs]`. Then use the resulting hypothesis. Establish `hnorm : ‖Complex.exp (z ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2)`. Rewrite using `[Complex.norm_exp]`. Use `congr 1`. Simplify using `[pow_two, hxdef, hydef]`.

Establish `hz : ‖z‖ ≤ |x| + |y|`. Rewrite using `[hxdef, hydef]`. Conclude with `Complex.norm_le_abs_re_add_abs_im z`. Take `⟨u, hudef⟩ : ∃ u : ℝ, u = T + |y|` from `⟨_, rfl⟩`. Establish `hy0` using `abs_nonneg y`.

Establish `hu1 : 1 ≤ u` using `by linarith`. Establish `h1z : 1 + ‖z‖ ≤ u` using `by linarith`. Take `⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (y ^ 2 / 2)` from `⟨_, rfl⟩`. Establish `hE0 : 0 < E` using `hEdef ▸ Real.exp_pos _`. Establish `hE : 1 + y ^ 2 / 2 ≤ E`.

Use `Real.add_one_le_exp (y ^ 2 / 2)` as an intermediate fact. Rewrite using `[hEdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hEE : E ^ 2 = Real.exp (y ^ 2)`. Rewrite using `[hEdef, ← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hu2 : u ^ 2 ≤ 4 * T ^ 2 * E`. Establish `hsq : |y| ^ 2 = y ^ 2` using `sq_abs y`.

Establish `hA : u ^ 2 ≤ 2 * T ^ 2 + 2 * y ^ 2`. Rewrite using `[hudef]`. Use polynomial arithmetic with `[sq_nonneg (T - |y|)]`. Establish `hT2 : 1 ≤ T ^ 2` using `one_le_pow₀ hT`. Establish `hC : 2 * T ^ 2 + 2 * y ^ 2 ≤ 4 * T ^ 2 * (1 + y ^ 2 / 2)`.

Use polynomial arithmetic with `[mul_nonneg (sq_nonneg y) (sub_nonneg.2 hT2), sq_nonneg T]`. Establish `hD : 4 * T ^ 2 * (1 + y ^ 2 / 2) ≤ 4 * T ^ 2 * E` using `mul_le_mul_of_nonneg_left hE (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu4 : u ^ 4 ≤ 16 * T ^ 4 * Real.exp (y ^ 2)`. Establish `h` using `pow_le_pow_left₀ (by positivity) hu2 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hz3 : (1 + ‖z‖) ^ 3 ≤ u ^ 4`. Establish `h0 : 0 ≤ 1 + ‖z‖` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (B ^ 2) * Real.exp (-y ^ 2)`.

Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hnorm]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem gauss_bound (b c : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3 ≤ M := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max |b| |c| := ⟨_, rfl⟩
  have hbB : |b| ≤ B := hB ▸ le_max_left _ _
  have hcB : |c| ≤ B := hB ▸ le_max_right _ _
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hbB
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + B := ⟨_, rfl⟩
  have hT : 1 ≤ T := by linarith
  refine ⟨16 * T ^ 4 * Real.exp (B ^ 2), by positivity, fun z h1 h2 => ?_⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = z.re := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = z.im := ⟨_, rfl⟩
  have hx : |x| ≤ B := by
    rw [abs_le]
    constructor
    · have := neg_abs_le b
      rw [hxdef]; linarith
    · have := le_abs_self c
      rw [hxdef]; linarith
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
  have hnorm : ‖Complex.exp (z ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, hxdef, hydef]
  have hz : ‖z‖ ≤ |x| + |y| := by
    rw [hxdef, hydef]; exact Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = T + |y| := ⟨_, rfl⟩
  have hy0 := abs_nonneg y
  have hu1 : 1 ≤ u := by linarith
  have h1z : 1 + ‖z‖ ≤ u := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (y ^ 2 / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ Real.exp_pos _
  have hE : 1 + y ^ 2 / 2 ≤ E := by
    have := Real.add_one_le_exp (y ^ 2 / 2)
    rw [hEdef]; linarith
  have hEE : E ^ 2 = Real.exp (y ^ 2) := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu2 : u ^ 2 ≤ 4 * T ^ 2 * E := by
    have hsq : |y| ^ 2 = y ^ 2 := sq_abs y
    have hA : u ^ 2 ≤ 2 * T ^ 2 + 2 * y ^ 2 := by
      rw [hudef]
      nlinarith [sq_nonneg (T - |y|)]
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hC : 2 * T ^ 2 + 2 * y ^ 2 ≤ 4 * T ^ 2 * (1 + y ^ 2 / 2) := by
      nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.2 hT2), sq_nonneg T]
    have hD : 4 * T ^ 2 * (1 + y ^ 2 / 2) ≤ 4 * T ^ 2 * E :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have hu4 : u ^ 4 ≤ 16 * T ^ 4 * Real.exp (y ^ 2) := by
    have h := pow_le_pow_left₀ (by positivity) hu2 2
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ ≤ (4 * T ^ 2 * E) ^ 2 := h
      _ = 16 * T ^ 4 * E ^ 2 := by ring
      _ = 16 * T ^ 4 * Real.exp (y ^ 2) := by rw [hEE]
  have hz3 : (1 + ‖z‖) ^ 3 ≤ u ^ 4 := by
    have h0 : 0 ≤ 1 + ‖z‖ := by positivity
    calc (1 + ‖z‖) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ h0 h1z 3
      _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hexp : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (B ^ 2) * Real.exp (-y ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  rw [hnorm]
  calc Real.exp (x ^ 2 - y ^ 2) * (1 + ‖z‖) ^ 3
      ≤ (Real.exp (B ^ 2) * Real.exp (-y ^ 2)) * (16 * T ^ 4 * Real.exp (y ^ 2)) :=
        mul_le_mul hexp (hz3.trans hu4) (by positivity) (by positivity)
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) * (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) := by ring
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) := by
        rw [← Real.exp_add]; simp

/- English proof (translation)
Introduce `a N ha`. Take `⟨hd, hg⟩` from `ha`. Establish `hE : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * a z` using `(Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul hd`. Establish `key : ∀ b c : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖) ≤ M`. Introduce `b c`.

Take `⟨M₁, hM₁, h₁⟩` from `gauss_bound b c`. Take `⟨M₂, h₂⟩` from `hg b c`. Use `⟨|M₂| * M₁, by positivity, fun z hb hc => ?_⟩` and prove the remaining obligations. Establish `hz` using `h₁ z hb hc`. Establish `ha' : ‖a z‖ ≤ |M₂| * (1 + ‖z‖) ^ 2` using `(h₂ z hb hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨hE, fun b c => ?_⟩, ⟨(differentiable_id.sub_const N).mul hE, fun b c => ?_⟩⟩` and prove the remaining obligations. Take `⟨M, _, h⟩` from `key b c`. Use `⟨M, fun z hb hc => (?_ : _ ≤ _).trans (h z hb hc)⟩` and prove the remaining obligations.

Conclude with `le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])`. Take `⟨M, hM, h⟩` from `key b c`. Use `⟨(1 + ‖N‖) * M, fun z hb hc => ?_⟩` and prove the remaining obligations. Establish `hzN : ‖z - N‖ ≤ (1 + ‖N‖) * (1 + ‖z‖)`. Use `norm_sub_le z N` as an intermediate fact.

Use polynomial arithmetic with `[norm_nonneg z, norm_nonneg N, mul_nonneg (norm_nonneg z) (norm_nonneg N)]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `h z hb hc` as an intermediate fact. Use `gcongr`.
-/
theorem dGood : DGood := by
  intro a N ha
  obtain ⟨hd, hg⟩ := ha
  have hE : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * a z :=
    (Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul hd
  have key : ∀ b c : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖) ≤ M := by
    intro b c
    obtain ⟨M₁, hM₁, h₁⟩ := gauss_bound b c
    obtain ⟨M₂, h₂⟩ := hg b c
    refine ⟨|M₂| * M₁, by positivity, fun z hb hc => ?_⟩
    have hz := h₁ z hb hc
    have ha' : ‖a z‖ ≤ |M₂| * (1 + ‖z‖) ^ 2 :=
      (h₂ z hb hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    rw [norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖a z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (|M₂| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M₂| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3) := by ring
      _ ≤ |M₂| * M₁ := by gcongr
  refine ⟨⟨hE, fun b c => ?_⟩, ⟨(differentiable_id.sub_const N).mul hE, fun b c => ?_⟩⟩
  · obtain ⟨M, _, h⟩ := key b c
    refine ⟨M, fun z hb hc => (?_ : _ ≤ _).trans (h z hb hc)⟩
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])
  · obtain ⟨M, hM, h⟩ := key b c
    refine ⟨(1 + ‖N‖) * M, fun z hb hc => ?_⟩
    have hzN : ‖z - N‖ ≤ (1 + ‖N‖) * (1 + ‖z‖) := by
      have := norm_sub_le z N
      nlinarith [norm_nonneg z, norm_nonneg N, mul_nonneg (norm_nonneg z) (norm_nonneg N)]
    rw [norm_mul]
    calc ‖z - N‖ * ‖Complex.exp (z ^ 2) * a z‖
        ≤ ((1 + ‖N‖) * (1 + ‖z‖)) * ‖Complex.exp (z ^ 2) * a z‖ := by gcongr
      _ = (1 + ‖N‖) * (‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖)) := by ring
      _ ≤ (1 + ‖N‖) * M := by
          have := h z hb hc
          gcongr

end GlobalTheory.CompanionTheory.RgEisDGood
