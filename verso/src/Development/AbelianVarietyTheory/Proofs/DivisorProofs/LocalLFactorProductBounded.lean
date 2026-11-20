import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ZetaPartial

open Formalism.L2.Host (aboveF)

variable {E : Type} [Field E] [NumberField E]

def invSq (w : HeightOneSpectrum (𝓞 E)) : ℝ := ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ))

/- English proof (translation)
Unfold `invSq`. Check the signs of the components of the expression.
-/
theorem invSq_nonneg (w : HeightOneSpectrum (𝓞 E)) : 0 ≤ invSq w := by unfold invSq; positivity

/- English proof (translation)
Establish `h` using `GlobalTheory.LFun.summable_rpow (K := E) ∅ (σ := 2) one_lt_two`. Conclude with `(Equiv.subtypeUnivEquiv (fun w => Set.notMem_empty w)).summable_iff.1 h`.
-/
theorem summable_invSq : Summable (invSq (E := E)) := by
  have h := GlobalTheory.LFun.summable_rpow (K := E) ∅ (σ := 2) one_lt_two
  exact (Equiv.subtypeUnivEquiv (fun w => Set.notMem_empty w)).summable_iff.1 h

/- English proof (translation)
Establish `hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast one_lt_absNorm w`. Establish `hN2 : (2 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)`. Use `one_lt_absNorm w` as an intermediate fact. Conclude with `this` after adjusting the coercions. Unfold `invSq`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem invSq_le_half (w : HeightOneSpectrum (𝓞 E)) : invSq w ≤ 1 / 2 := by
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast one_lt_absNorm w
  have hN2 : (2 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    have := one_lt_absNorm w
    exact_mod_cast this
  unfold invSq
  calc ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by norm_num)
    _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hN2
    _ = 1 / 2 := by norm_num

/- English proof (translation)
Establish `hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast one_lt_absNorm w`. Establish `e : locL (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) w (s : ℂ) = (1 - npow w (-(s : ℂ)))⁻¹`. Simplify using `[locL]`. Use `set z := npow w (-(s : ℂ)) with hzdef`. Establish `hz : ‖z‖ ≤ invSq w`.

Rewrite using `[hzdef, norm_npow]`. Simplify using `only [Complex.neg_re, Complex.natCast_re]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hN.le (by have : (2 : ℝ) ≤ s := (by exact_mod_cast hs); linarith)`. Establish `hh` using `invSq_le_half w`. Establish `h1 : 1 - ‖z‖ ≤ ‖1 - z‖` using `by simpa using norm_sub_norm_le (1 : ℂ) z`.

Establish `hpos : 0 < 1 - ‖z‖` using `by linarith`. Rewrite using `[e, norm_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hm` using `inv_mul_cancel₀ hpos.ne'`. Establish `hi` using `inv_pos.2 hpos`.

Use polynomial arithmetic with `[norm_nonneg z]`. Use `_ ≤ 1 + 2 * invSq w := by linarith`. Use `_ ≤ Real.exp (2 * invSq w) := by linarith [Real.add_one_le_exp (2 * invSq w)]`.
-/
theorem norm_locL_le (w : HeightOneSpectrum (𝓞 E)) {s : ℕ} (hs : 2 ≤ s) :
    ‖locL (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) w (s : ℂ)‖ ≤ Real.exp (2 * invSq w) := by
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast one_lt_absNorm w
  have e : locL (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) w (s : ℂ) = (1 - npow w (-(s : ℂ)))⁻¹ := by
    simp [locL]
  set z := npow w (-(s : ℂ)) with hzdef
  have hz : ‖z‖ ≤ invSq w := by
    rw [hzdef, norm_npow]
    simp only [Complex.neg_re, Complex.natCast_re]
    exact Real.rpow_le_rpow_of_exponent_le hN.le (by have : (2 : ℝ) ≤ s := (by exact_mod_cast hs); linarith)
  have hh := invSq_le_half w
  have h1 : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le (1 : ℂ) z
  have hpos : 0 < 1 - ‖z‖ := by linarith
  rw [e, norm_inv]
  calc ‖1 - z‖⁻¹ ≤ (1 - ‖z‖)⁻¹ := inv_anti₀ hpos h1
    _ ≤ 1 + 2 * ‖z‖ := by
        have hm := inv_mul_cancel₀ hpos.ne'
        have hi := inv_pos.2 hpos
        nlinarith [norm_nonneg z]
    _ ≤ 1 + 2 * invSq w := by linarith
    _ ≤ Real.exp (2 * invSq w) := by linarith [Real.add_one_le_exp (2 * invSq w)]

/- English proof (translation)
Introduce `F E _ _ _ _ _ s hs`. Use `⟨Real.exp (2 * ∑' w, invSq (E := E) w), fun S => ?_⟩` and prove the remaining obligations. Establish `hdisj : (S : Set (HeightOneSpectrum (𝓞 F))).PairwiseDisjoint (fun v => aboveF (L` using `E) F v) := fun v _ v' _ hne => Finset.disjoint_left.2 fun w h1 h2 => hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2))`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_` and prove the remaining obligations.

Unfold `Lv`. Conclude with `(Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w _ => norm_locL_le w hs)`. Use `_ = ∏ w ∈ S.biUnion (fun v => aboveF (L := E) F v), Real.exp (2 * invSq w) := (Finset.prod_biUnion hdisj).symm`. Use `_ = Real.exp (2 * ∑ w ∈ S.biUnion (fun v => aboveF (L := E) F v), invSq w) := by`. Rewrite using `[← Real.exp_sum, Finset.mul_sum]`.

Use `_ ≤ Real.exp (2 * ∑' w, invSq (E := E) w) := by`. Use `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))` and prove the remaining obligations. Conclude with `summable_invSq.sum_le_tsum _ (fun w _ => invSq_nonneg w)`.
-/
theorem prod_norm_Lv_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s : ℕ),
    2 ≤ s → ∃ C : ℝ, ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ S, ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ)‖ ≤ C := by
  intro F E _ _ _ _ _ s hs
  classical
  refine ⟨Real.exp (2 * ∑' w, invSq (E := E) w), fun S => ?_⟩
  have hdisj : (S : Set (HeightOneSpectrum (𝓞 F))).PairwiseDisjoint (fun v => aboveF (L := E) F v) :=
    fun v _ v' _ hne => Finset.disjoint_left.2 fun w h1 h2 =>
      hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2))
  calc ∏ v ∈ S, ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ)‖
        ≤ ∏ v ∈ S, ∏ w ∈ aboveF (L := E) F v, Real.exp (2 * invSq w) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
          unfold Lv
          exact (Finset.norm_prod_le _ _).trans
            (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w _ => norm_locL_le w hs)
    _ = ∏ w ∈ S.biUnion (fun v => aboveF (L := E) F v), Real.exp (2 * invSq w) :=
          (Finset.prod_biUnion hdisj).symm
    _ = Real.exp (2 * ∑ w ∈ S.biUnion (fun v => aboveF (L := E) F v), invSq w) := by
          rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ∑' w, invSq (E := E) w) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          exact summable_invSq.sum_le_tsum _ (fun w _ => invSq_nonneg w)

end GlobalTheory.ZetaPartial
