import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DedekindZetaEqSumRealEisenstein
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

/- English proof (translation)
Introduce `s hs`. Establish `hs0 : (0 : ℝ) < s` using `by linarith`. Use `⟨Quadratic.dedekindZeta_eq_mul K (by simpa using hs), ?_⟩` and prove the remaining obligations. Set `f : (Ideal (𝓞 K))⁰ → ℝ` to `fun I ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)`. Establish `hf : ∀ I, 0 ≤ f I` using `fun I ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _`.

Set `g : ClassGroup (𝓞 K) → ENNReal` to `fun C ↦ ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), ENNReal.ofReal (f I)`. Establish `htot : ENNReal.ofReal (dedekindZetaReal K s) = ∑ C, g C` using `(GroundTheory.Heights₂.Theta.projectiveLineClassData.ofReal_dedekindZetaReal K hs).trans (GroundTheory.Heights₂.Theta.projectiveLineClassData.tsum_ideal_eq_sum_class K hs0)`. Establish `hg : ∀ C, g C ≠ ⊤` using `fun C ↦ by`. Use `ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := dedekindZetaReal K s)) ?_` and prove the remaining obligations. Rewrite using `[htot]`.

Conclude with `Finset.single_le_sum (f := g) (fun _ _ ↦ zero_le) (Finset.mem_univ C)`. Establish `hpz : ∀ C, partialZeta C s = ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), f I` using `fun C ↦ by`. Use `tsum_congr fun I ↦ ?_` and prove the remaining obligations. Conclude with `(Real.rpow_neg (Nat.cast_nonneg _) s).symm`. Establish `hsum : ∀ C, Summable fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I` using `fun C ↦ by simpa [ENNReal.toReal_ofReal (hf _)] using ENNReal.summable_toReal (hg C)`.

Establish `hofr : ∀ C, ENNReal.ofReal (partialZeta C s) = g C` using `fun C ↦ by`. Rewrite using `[hpz]`. Conclude with `ENNReal.ofReal_tsum_of_nonneg (f := fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I) (fun I ↦ hf I) (hsum C)`. Establish `hnn : ∀ C, 0 ≤ partialZeta C s` using `fun C ↦ by`. Rewrite using `[hpz]`.

Conclude with `tsum_nonneg fun I ↦ hf I`. Establish `hreal : ∑ C : ClassGroup (𝓞 K), partialZeta C s = dedekindZetaReal K s`. Establish `hζ : 0 ≤ dedekindZetaReal K s` using `tsum_nonneg fun n ↦ dedekindZetaTerm_nonneg K s n`. Use `(ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun C _ ↦ hnn C) hζ).1 ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun C _ ↦ hnn C), htot]`.

Conclude with `Finset.sum_congr rfl (fun C _ ↦ hofr C)`. Rewrite using `[dedekindZeta_ofReal K hs0.ne', ← hreal]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ZetaFactor.proof (S : PrimeDiscriminant K) : ZetaFactor.Statement S := by
  intro s hs
  have hs0 : (0 : ℝ) < s := by linarith
  refine ⟨Quadratic.dedekindZeta_eq_mul K (by simpa using hs), ?_⟩

  let f : (Ideal (𝓞 K))⁰ → ℝ := fun I ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)
  have hf : ∀ I, 0 ≤ f I := fun I ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  let g : ClassGroup (𝓞 K) → ENNReal := fun C ↦
    ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), ENNReal.ofReal (f I)
  have htot : ENNReal.ofReal (dedekindZetaReal K s) = ∑ C, g C :=
    (GroundTheory.Heights₂.Theta.projectiveLineClassData.ofReal_dedekindZetaReal K hs).trans
      (GroundTheory.Heights₂.Theta.projectiveLineClassData.tsum_ideal_eq_sum_class K hs0)
  have hg : ∀ C, g C ≠ ⊤ := fun C ↦ by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := dedekindZetaReal K s)) ?_
    rw [htot]
    exact Finset.single_le_sum (f := g) (fun _ _ ↦ zero_le) (Finset.mem_univ C)

  have hpz : ∀ C, partialZeta C s =
      ∑' I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰), f I := fun C ↦ by
    refine tsum_congr fun I ↦ ?_
    exact (Real.rpow_neg (Nat.cast_nonneg _) s).symm
  have hsum : ∀ C, Summable fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I :=
    fun C ↦ by simpa [ENNReal.toReal_ofReal (hf _)] using ENNReal.summable_toReal (hg C)
  have hofr : ∀ C, ENNReal.ofReal (partialZeta C s) = g C := fun C ↦ by
    rw [hpz]
    exact ENNReal.ofReal_tsum_of_nonneg (f := fun I : (ClassGroup.mk0 ⁻¹' {C} : Set (Ideal (𝓞 K))⁰) ↦ f I)
      (fun I ↦ hf I) (hsum C)
  have hnn : ∀ C, 0 ≤ partialZeta C s := fun C ↦ by
    rw [hpz]
    exact tsum_nonneg fun I ↦ hf I
  have hreal : ∑ C : ClassGroup (𝓞 K), partialZeta C s = dedekindZetaReal K s := by
    have hζ : 0 ≤ dedekindZetaReal K s := tsum_nonneg fun n ↦ dedekindZetaTerm_nonneg K s n
    refine (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun C _ ↦ hnn C) hζ).1 ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun C _ ↦ hnn C), htot]
    exact Finset.sum_congr rfl (fun C _ ↦ hofr C)
  rw [dedekindZeta_ofReal K hs0.ne', ← hreal]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
