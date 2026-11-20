import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLeStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Introduce `l _ h j r y hh hr hy`. Establish `hl : ‖(l : ℂ_[l])‖ < 1` using `GlobalTheory.RingBasics.norm_p_lt`. Establish `hl0 : 0 ≤ ‖(l : ℂ_[l])‖` using `norm_nonneg _`. Establish `hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r` using `fun k => (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (y k) hh hr (hy k)).2.1`. Establish `hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r`.

Introduce `k`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)`. Establish `hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k))` using `Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm`. Establish `hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y)` using `hsum.hasSum`.

Establish `hg0 : 0 ≤ gam l h j r` using `le_trans (norm_nonneg _) (hlam 0)`. Use `⟨hHas, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0} (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by` as an intermediate fact. Introduce `k hk`. Establish `hk1 : 1 ≤ k` using `Nat.one_le_iff_ne_zero.mpr (by simpa using hk)`.

Use `le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)` and prove the remaining obligations. Simplify using `using pow_le_pow_of_le_one hl0 hl.le hk1)`. Simplify using `using this`. Use `GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅ (gam l h j r) hg0 hHas (by` as an intermediate fact. Introduce `k _`.

Use `le_trans (hterm k) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `using this`. Establish `hsh` using `GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l`. Establish `key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x`.

Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `succ N ih`.

Introduce `x hx`. Establish `hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r`. Rewrite using `[hsh.2.2.2.1, norm_pow]`. Establish `h1 : ‖sh x‖ ≤ 1` using `hsh.2.2.2.2.1 x`. Establish `hpos : 1 ≤ l ^ (h * N)` using `Nat.one_le_pow _ _ (Fact.out : l.Prime).pos`.

Conclude with `le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx`. Establish `e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h`. Rewrite using `[← pow_mul, ← pow_add, Nat.mul_succ]`. Rewrite using `[e, (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `N`. Unfold `abelian₂`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[key N (y k) (hy k)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Lam_main : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  intro l _ h j r y hh hr hy
  have hl : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r := fun k =>
    (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (y k) hh hr (hy k)).2.1
  have hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r := by
    intro k
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm
  have hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) := hsum.hasSum
  have hg0 : 0 ≤ gam l h j r := le_trans (norm_nonneg _) (hlam 0)
  refine ⟨hHas, ?_, ?_, ?_⟩
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0}
      (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by
        intro k hk
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
        refine le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)
        simpa using pow_le_pow_of_le_one hl0 hl.le hk1)
    simpa using this
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅
      (gam l h j r) hg0 hHas (by
        intro k _
        refine le_trans (hterm k) ?_
        calc ‖(l : ℂ_[l])‖ ^ k * gam l h j r ≤ 1 * gam l h j r :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl.le) hg0
          _ = gam l h j r := one_mul _)
    simpa using this
  · have hsh := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l

    have key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x := by
      intro N
      induction N with
      | zero => intro x _; simp
      | succ N ih =>
        intro x hx
        have hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r := by
          rw [hsh.2.2.2.1, norm_pow]
          have h1 : ‖sh x‖ ≤ 1 := hsh.2.2.2.2.1 x
          have hpos : 1 ≤ l ^ (h * N) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
          exact le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx
        have e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h := by
          rw [← pow_mul, ← pow_add, Nat.mul_succ]
        rw [e, (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]
        ring
    intro N
    unfold abelian₂
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [key N (y k) (hy k)]
    ring

end GlobalTheory.PSer
