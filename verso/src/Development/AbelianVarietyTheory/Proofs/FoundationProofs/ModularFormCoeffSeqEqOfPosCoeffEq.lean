import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨C, A, hC⟩` from `ha`. Use `set r : ℝ := Real.exp (-2 * π * τ.im) with hr`. Establish `hr0 : 0 < r` using `Real.exp_pos _`. Establish `hr1 : r < 1`. Rewrite using `[hr, ← Real.exp_zero, Real.exp_lt_exp]`.

Use `τ.im_pos` as an intermediate fact. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `hnorm : ∀ n : ℕ, ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n`. Introduce `n`. Rewrite using `[Complex.norm_exp, hr, ← Real.exp_nat_mul]`.

Use `congr 1`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n`. Establish `h0 : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n` using `summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)`.

Establish `h1` using `(summable_nat_add_iff 1).mpr h0`. Establish `h2` using `h1.mul_left r⁻¹`. Use `h2.congr fun n => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts. Use `Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg.mul_left C)` and prove the remaining obligations. Rewrite using `[norm_mul, hnorm n, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0.le n)`.
-/
lemma summable_norm_qterm_of_polyB (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r : ℝ := Real.exp (-2 * π * τ.im) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero, Real.exp_lt_exp]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  have hnorm : ∀ n : ℕ, ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
    intro n
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
    have h0 : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr fun n => ?_
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg.mul_left C)
  rw [norm_mul, hnorm n, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0.le n)

end GlobalTheory.EisM

namespace GlobalTheory.EisM

/- English proof (translation)
Unfold `qs`. Rewrite using `[← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]`. Rewrite using `[tsum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `n hn`.

Rewrite using `[hab n hn, sub_self]`.
-/
lemma qs_sub_eq_const (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) (hab : ∀ n, n ≠ 0 → a n = b n) (τ : ℍ) :
    qs a τ - qs b τ = a 0 - b 0 := by
  unfold qs
  rw [← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [hab n hn, sub_self]

/- English proof (translation)
Introduce `k L χ a b hk hL ha hb hab`. Use `set c : ℂ := a 0 - b 0 with hc`. Establish `hconst` using `qs_sub_eq_const a b ha.1 hb.1 hab`. Set `γ : SL(2, ℤ)` to `⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩`. Establish `hγ10 : γ 1 0 = (L : ℤ)` using `rfl`.

Establish `hγ11 : γ 1 1 = 1` using `rfl`. Establish `key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c`. Introduce `τ`. Establish `h1` using `ha.2 γ (by rw [hγ10]) τ`. Establish `h2` using `hb.2 γ (by rw [hγ10]) τ`.

Rewrite `h1`, `h2` using `[hγ10, hγ11]`. Establish `e1` using `hconst (γ • τ)`. Rewrite `e1` using `[h1, h2, ← mul_sub, hconst τ, ← hc]`. Move the coercions through the operations in `at e1`. Conclude with `e1.symm`.

Assume the negation of the conclusion as `hne`. Establish `hc0 : c ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `n`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Conclude with `sub_eq_zero.mp h0`. Conclude with `hab n hn`. Establish `hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1`. Introduce `τ`.

Establish `h` using `key τ`. Establish `h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1`. Establish `: (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0` using `by rw [sub_mul, ← h]; ring`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)`. Rewrite using `[← norm_pow, ← norm_mul, h', norm_one]`.

Set `τ₁ : ℍ` to `⟨Complex.I, by simp⟩`. Set `τ₂ : ℍ` to `⟨2 * Complex.I, by simp⟩`. Establish `e1` using `hone τ₁`. Establish `e2` using `hone τ₂`. Establish `hχ : ‖χ 1‖ ≠ 0`.

Introduce `h0`. Rewrite `e1` using `[h0, zero_mul]`. Conclude with `zero_ne_one e1`. Establish `heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k` using `mul_left_cancel₀ hχ (e1.trans e2.symm)`. Establish `hL' : (0 : ℝ) < L` using `by exact_mod_cast hL`.

Establish `hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖`. Establish `s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[τ₁, UpperHalfPlane.coe_mk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[τ₂, UpperHalfPlane.coe_mk]`. Expand and normalize the polynomial expressions, which then agree. Establish `: ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2`.

Rewrite using `[s1, s2]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this`. Use `pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)` as an intermediate fact. Conclude with `absurd heq (ne_of_lt this)`.
-/
theorem eq_of_coeff_pos_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b →
    (∀ n, n ≠ 0 → a n = b n) → a = b := by
  intro k L χ a b hk hL ha hb hab
  set c : ℂ := a 0 - b 0 with hc
  have hconst := qs_sub_eq_const a b ha.1 hb.1 hab
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ10 : γ 1 0 = (L : ℤ) := rfl
  have hγ11 : γ 1 1 = 1 := rfl
  have key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c := by
    intro τ
    have h1 := ha.2 γ (by rw [hγ10]) τ
    have h2 := hb.2 γ (by rw [hγ10]) τ
    rw [hγ10, hγ11] at h1 h2
    have e1 := hconst (γ • τ)
    rw [h1, h2, ← mul_sub, hconst τ, ← hc] at e1
    push_cast at e1
    exact e1.symm
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · exact sub_eq_zero.mp h0
    · exact hab n hn
  have hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1 := by
    intro τ
    have h := key τ
    have h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1 := by
      have : (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0 := by rw [sub_mul, ← h]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [← norm_pow, ← norm_mul, h', norm_one]
  let τ₁ : ℍ := ⟨Complex.I, by simp⟩
  let τ₂ : ℍ := ⟨2 * Complex.I, by simp⟩
  have e1 := hone τ₁
  have e2 := hone τ₂
  have hχ : ‖χ 1‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact zero_ne_one e1
  have heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k :=
    mul_left_cancel₀ hχ (e1.trans e2.symm)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖ := by
    have s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₁, UpperHalfPlane.coe_mk]
      ring
    have s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₂, UpperHalfPlane.coe_mk]
      ring
    have : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2 := by
      rw [s1, s2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)
  exact absurd heq (ne_of_lt this)

end GlobalTheory.EisM
