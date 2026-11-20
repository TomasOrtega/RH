import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

/- English proof (translation)
Use `le_trans ?_ (𝓕.lam_le n)` and prove the remaining obligations. Unfold `LFam.lamChi`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]`.
-/
theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

/- English proof (translation)
Establish `h` using `(ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)`. Use `Summable.of_norm_bounded h.norm fun n => ?_` and prove the remaining obligations. Use `LSeries.norm_term_le s ?_` and prove the remaining obligations. Use `(norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[abs_of_nonneg vonMangoldt_nonneg]`.
-/
theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

/- English proof (translation)
Establish `h` using `(summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum`. Establish `h2` using `Complex.hasSum_re h`. Use `h2 using 2 with n` and compare the differences between its conclusion and the goal. Distinguish the cases in `hn : n = 0`. Simplify using `[hn]`.

Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn`. Rewrite using `[LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg hn, ← Complex.re_ofReal_mul]`. Use `congr 1`.

Rewrite using `[div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']`. Use `push_cast`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Both sides reduce to the same expression.
-/
theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

/- English proof (translation)
Simplify using `using hasSum_re 𝓕 χ σ 0 hs rfl`.
-/
theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

/- English proof (translation)
Use `split_ifs`. Conclude with `le_rfl`. Conclude with `mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)`.
-/
theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/- English proof (translation)
Establish `: χ g * χ g = 1`. Use `congrArg (fun φ : AddChar G ℂ => φ g) h` as an intermediate fact. Simplify using `using this`. Conclude with `mul_self_eq_one_iff.mp this`.
-/
theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

/- English proof (translation)
Establish `h : z.re * z.re + z.im * z.im = 1`. Rewrite using `[← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]`. Evaluate the numerical expressions. Rewrite using `[Complex.mul_re]`. Use polynomial arithmetic with `[sq_nonneg (z.re + 1)]`.
-/
theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

/- English proof (translation)
Introduce `𝓕 χ ψ σ t hσ`. Establish `h1` using `hasSum_re₀ 𝓕 1 σ hσ`. Use `⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h2` using `hasSum_re 𝓕 χ σ (t * I) hσ (by simp)`. Establish `h3` using `hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)`.

Use `HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)` and prove the remaining obligations. Distinguish the cases in `hn : n = 0`. Simplify using `[hn]`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Use `Finset.sum_nonneg fun g _ => ?_` and prove the remaining obligations. Establish `hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1`. Rewrite using `[norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]`. Simplify using the standard rewrite rules. Establish `ht` using `trig _ hz`.

Establish `he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I)))`. Rewrite using `[show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, AddChar.one_apply, Complex.one_re]`. Use `mul_nonneg (w_nonneg 𝓕 σ n g) ht` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1` and prove the remaining obligations. Rewrite using `[AddChar.one_apply, Complex.one_re, mul_one]`. Conclude with `w_nonneg 𝓕 σ n g`. Use `HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_nonneg fun g _ => ?_` and prove the remaining obligations. Establish `hw` using `w_nonneg 𝓕 σ n g`. Rewrite using `[AddChar.one_apply]`. Apply the tactic sequence `rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith`.

Use `HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_nonneg fun g _ => ?_` and prove the remaining obligations. Establish `hw` using `w_nonneg 𝓕 σ n g`. Rewrite using `[AddChar.one_apply, AddChar.mul_apply]`.

Apply the tactic sequence `rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>`. Apply the tactic sequence `simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith`.
-/
theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
