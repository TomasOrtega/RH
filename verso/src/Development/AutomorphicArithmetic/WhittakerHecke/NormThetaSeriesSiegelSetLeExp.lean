import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.WhittakerHecke.SummableTsumInvOneAddHeightPowLe
import Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatTranslateDecayBound
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsCommonDenomOfIsCompactUnipotentTranslates
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatMulIdeleFinitePartMemCompactOfLeNorm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.QuaternionSwap

private noncomputable def Yv (b : A ℚ) (a : (A ℚ)ˣ) (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ :=
  ![rt (ξ 0) * (a : A ℚ), (rt (ξ 0) * b + rt (ξ 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)]

/- English proof (translation)
Establish `h1 : (gl (nU b * mD a) * k).val = (nU b * mD a).val * k.val` using `rfl`. Rewrite using `[h1, ← Matrix.vecMul_vecMul]`. Use `congr 1`. Establish `h2 : (nU b * mD a).val = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)]` using `rfl`. Rewrite using `[h2]`.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `fin_cases j <;> simp [Yv, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring`.
-/
private theorem row_eq (b : A ℚ) (a : (A ℚ)ˣ) (k : GL (Fin 2) (A ℚ)) (ξ : Fin 2 → ℚ) :
    (fun i => rt (ξ i)) ᵥ* (gl (nU b * mD a) * k).val = Yv b a ξ ᵥ* k.val := by
  have h1 : (gl (nU b * mD a) * k).val = (nU b * mD a).val * k.val := rfl
  rw [h1, ← Matrix.vecMul_vecMul]
  congr 1
  have h2 : (nU b * mD a).val = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [h2]
  funext j
  fin_cases j <;> simp [Yv, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

private def swapQ (q : ℚ) (hq : q ≠ 0) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨![q * ξ.1 0, q⁻¹ * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  invFun ξ := ⟨![q⁻¹ * ξ.1 0, q * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]
  right_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]

/- English proof (translation)
Establish `hqq : rt q * rt q⁻¹ = (1 : A ℚ)`. Rewrite using `[← map_mul, mul_inv_cancel₀ hq, map_one]`. Establish `hinv : ((a'⁻¹ : (A ℚ)ˣ) : A ℚ) = rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[ha]`.

Combine the equalities or inequalities in the displayed calculation. Establish `rm : ∀ x y : ℚ, rt (x * y) = rt x * rt y` using `fun x y => map_mul (algebraMap ℚ (A ℚ)) x y`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Express the relevant statement in the definitionally equal form `rt (q * ξ.1 0) * (a : A ℚ) = rt (ξ.1 0) * (a' : A ℚ)`.

Rewrite using `[ha, rm]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(rt (q * ξ.1 0) * b + rt (q⁻¹ * ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = (rt (ξ.1 0) * (rt (q ^ 2) * b) + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ)`. Establish `e2 : rt (q ^ 2) = rt q * rt q` using `by rw [pow_two, rm]`. Rewrite using `[hinv, rm, rm, e2]`.

Establish `e : rt q = rt q * rt q * rt q⁻¹` using `by rw [mul_assoc, hqq, mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem Yv_swap (q : ℚ) (hq : q ≠ 0) (b : A ℚ) (a a' : (A ℚ)ˣ) (ha : (a' : A ℚ) = rt q * (a : A ℚ))
    (ξ : Rw ℚ) : Yv b a (swapQ q hq ξ).1 = Yv (rt (q ^ 2) * b) a' ξ.1 := by
  have hqq : rt q * rt q⁻¹ = (1 : A ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have hinv : ((a'⁻¹ : (A ℚ)ˣ) : A ℚ) = rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha]
    calc rt q * (a : A ℚ) * (rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ))
        = (rt q * rt q⁻¹) * ((a : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) := by ring
      _ = 1 := by rw [hqq, Units.mul_inv, one_mul]
  have rm : ∀ x y : ℚ, rt (x * y) = rt x * rt y := fun x y => map_mul (algebraMap ℚ (A ℚ)) x y
  funext j
  fin_cases j
  · change rt (q * ξ.1 0) * (a : A ℚ) = rt (ξ.1 0) * (a' : A ℚ)
    rw [ha, rm]
    ring
  · change (rt (q * ξ.1 0) * b + rt (q⁻¹ * ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) =
      (rt (ξ.1 0) * (rt (q ^ 2) * b) + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ)
    have e2 : rt (q ^ 2) = rt q * rt q := by rw [pow_two, rm]
    rw [hinv, rm, rm, e2]
    have e : rt q = rt q * rt q * rt q⁻¹ := by rw [mul_assoc, hqq, mul_one]
    calc (rt q * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)
        = ((rt q * rt q * rt q⁻¹) * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by rw [← e]
      _ = _ := by ring

/- English proof (translation)
Simplify using `[re, map_mul]`.
-/
private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re, map_mul]
/- English proof (translation)
Simplify using `[re, map_add]`.
-/
private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re, map_add]
/- English proof (translation)
Use `(InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal Rat.infinitePlace) (WithAbs.toAbs _ q)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem re_rat (q : ℚ) : re (rt q) = (q : ℝ) := by
  refine (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal Rat.infinitePlace) (WithAbs.toAbs _ q)).trans ?_
  simp
/- English proof (translation)
Establish `h : re (a : A ℚ) * re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = 1`. Rewrite using `[← re_mul, Units.mul_inv]`. Simplify using `[re]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
private theorem re_inv (a : (A ℚ)ˣ) : re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = (re (a : A ℚ))⁻¹ := by
  have h : re (a : A ℚ) * re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
    rw [← re_mul, Units.mul_inv]
    simp [re]
  exact eq_inv_of_mul_eq_one_right h

end UpperTheory.QuaternionSwap

open UpperTheory.QuaternionSwap in
/- English proof (translation)
Introduce `Φ hΦ C hC c hc n`. Take `⟨B0, κ, L, hB0, hκ, hκ1, hL, hmaj⟩` from `UpperTheory.schwartzBruhat_translate_decay_bound Φ hΦ C hC (n + 4)`. Take `⟨S, Bu, hS, hBu, hred⟩` from `UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm c hc`. Take `⟨d, hd, hden⟩` from `UpperTheory.exists_common_denom_of_isCompact_unipotent_translates L hL S hS`. Take `⟨B1, hB1, hsum⟩` from `UpperTheory.summable_tsum_inv_one_add_height_pow_le n d κ Bu hd hκ hκ1 hBu`.

Use `⟨n + 2, B0 * B1 * (Bu / c) ^ (n + 2), fun t ht b a k hk hca => ?_⟩` and prove the remaining obligations. Take `⟨q, a', u, hq, ha', hu, hf, hfi, hlo, hhi⟩` from `hred a hca`. Use `set b' : A ℚ := rt (q ^ 2) * b with hb'`. Use `set α : ℝ := |re (a' : A ℚ)| with hα`. Use `set β : ℝ := re b' with hβ`.

Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.2 (by linarith)) hlo`. Establish `hab : 0 < ab a` using `lt_of_lt_of_le hc hca`. Use `set T : ℝ := Bu * (ab a / c) with hT`. Establish `hT1 : 1 ≤ T`. Establish `: 1 ≤ ab a / c` using `(one_le_div hc).2 hca`.

Use the polynomial consequences of the given equalities and inequalities. Set `R : Set (Rw ℚ)` to `{ξ | (fun j => (Yv b' a' ξ.1 j).2) ∈ L}`. Set `Wt : Rw ℚ → ℝ` to `fun ξ => ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹`. Establish `hfin : ∀ ξ : Fin 2 → ℚ, (fun j => (Yv b' a' ξ j).2) = ![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2, (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b'.2 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]`. Introduce `ξ`.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Express the relevant statement in the definitionally equal form `(rt (ξ 0)).2 * (a' : A ℚ).2 = _`. Rewrite using `[hf]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `((rt (ξ 0)).2 * b'.2 + (rt (ξ 1)).2) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _`. Rewrite using `[hfi]`. Both sides reduce to the same expression. Establish `hR : ∀ ξ ∈ R, ∀ ξ' ∈ R, _` using `fun ξ h ξ' h' => hden u hu b'.2 ξ.1 ξ'.1 (by have := h; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this) (by have := h'; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)`. Take `⟨hs, hle⟩` from `hsum R β α T t ht hlo hhi hT1 (fun ξ h => (hR ξ h ξ h).1) (fun ξ h => (hR ξ h ξ h).2.1) (fun ξ h ξ' h' => (hR ξ h ξ' h').2.2)`.

Establish `hterm : ∀ ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ ≤ B0 * R.indicator Wt ξ`. Introduce `ξ`. Take `⟨h1, h2⟩` from `hmaj t k hk (Yv b' a' ξ.1)`. Establish `e0 : |re (Yv b' a' ξ.1 0)| = |((ξ.1 0 : ℚ) : ℝ)| * α`. Express the relevant statement in the definitionally equal form `|re (rt (ξ.1 0) * (a' : A ℚ))| = _`.

Rewrite using `[re_mul, re_rat, abs_mul]`. Establish `e1 : |re (Yv b' a' ξ.1 1)| = |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α`. Express the relevant statement in the definitionally equal form `|re ((rt (ξ.1 0) * b' + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ))| = _`. Rewrite using `[re_mul, re_add, re_mul, re_rat, re_rat, re_inv, abs_mul, abs_inv, div_eq_mul_inv]`. Distinguish the cases in `hξ : ξ ∈ R`.

Rewrite using `[Set.indicator_of_mem hξ]`. Rewrite `h1` using `[e0, e1]`. Conclude with `h1`. Rewrite using `[Set.indicator_of_notMem hξ, mul_zero]`. Establish `h0 : (Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hξ (h2 h)`. Rewrite using `[h0, norm_zero]`. Establish `hrew : ThR Φ t (gl (nU b * mD a) * k) = ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j`. Unfold `ThR`.

Rewrite using `[← (swapQ q hq).tsum_eq]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[row_eq, Yv_swap q hq b a a' ha' ξ]`. Establish `hsn : Summable fun ξ : Rw ℚ => ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B0)`. Rewrite using `[hrew]`.

Combine the equalities or inequalities in the displayed calculation. Establish `: T = Bu / c * ab a` using `by rw [hT]; ring`. Rewrite using `[this, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.norm_thetaSeries_siegelSet_le_exp :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi ℚ (Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ n : ℕ,
        ∃ (r : ℕ) (B : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a →
          ‖ThR Φ t (gl (nU b * mD a) * k)‖ ≤ B * Real.exp (-((n : ℝ) * t)) * ab a ^ r := by
  intro Φ hΦ C hC c hc n
  obtain ⟨B0, κ, L, hB0, hκ, hκ1, hL, hmaj⟩ := UpperTheory.schwartzBruhat_translate_decay_bound Φ hΦ C hC (n + 4)
  obtain ⟨S, Bu, hS, hBu, hred⟩ := UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm c hc
  obtain ⟨d, hd, hden⟩ := UpperTheory.exists_common_denom_of_isCompact_unipotent_translates L hL S hS
  obtain ⟨B1, hB1, hsum⟩ := UpperTheory.summable_tsum_inv_one_add_height_pow_le n d κ Bu hd hκ hκ1 hBu
  refine ⟨n + 2, B0 * B1 * (Bu / c) ^ (n + 2), fun t ht b a k hk hca => ?_⟩
  obtain ⟨q, a', u, hq, ha', hu, hf, hfi, hlo, hhi⟩ := hred a hca
  set b' : A ℚ := rt (q ^ 2) * b with hb'
  set α : ℝ := |re (a' : A ℚ)| with hα
  set β : ℝ := re b' with hβ
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.2 (by linarith)) hlo
  have hab : 0 < ab a := lt_of_lt_of_le hc hca
  set T : ℝ := Bu * (ab a / c) with hT
  have hT1 : 1 ≤ T := by
    have : 1 ≤ ab a / c := (one_le_div hc).2 hca
    nlinarith
  let R : Set (Rw ℚ) := {ξ | (fun j => (Yv b' a' ξ.1 j).2) ∈ L}
  let Wt : Rw ℚ → ℝ := fun ξ =>
    ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
  have hfin : ∀ ξ : Fin 2 → ℚ, (fun j => (Yv b' a' ξ j).2) =
      ![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b'.2 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) *
          ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2] := by
    intro ξ
    funext j
    fin_cases j
    · change (rt (ξ 0)).2 * (a' : A ℚ).2 = _
      rw [hf]
      rfl
    · change ((rt (ξ 0)).2 * b'.2 + (rt (ξ 1)).2) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
      rw [hfi]
      rfl
  have hR : ∀ ξ ∈ R, ∀ ξ' ∈ R, _ := fun ξ h ξ' h' =>
    hden u hu b'.2 ξ.1 ξ'.1 (by have := h; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
      (by have := h'; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
  obtain ⟨hs, hle⟩ := hsum R β α T t ht hlo hhi hT1 (fun ξ h => (hR ξ h ξ h).1) (fun ξ h => (hR ξ h ξ h).2.1)
    (fun ξ h ξ' h' => (hR ξ h ξ' h').2.2)
  have hterm : ∀ ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ ≤ B0 * R.indicator Wt ξ := by
    intro ξ
    obtain ⟨h1, h2⟩ := hmaj t k hk (Yv b' a' ξ.1)
    have e0 : |re (Yv b' a' ξ.1 0)| = |((ξ.1 0 : ℚ) : ℝ)| * α := by
      change |re (rt (ξ.1 0) * (a' : A ℚ))| = _
      rw [re_mul, re_rat, abs_mul]
    have e1 : |re (Yv b' a' ξ.1 1)| = |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      change |re ((rt (ξ.1 0) * b' + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ))| = _
      rw [re_mul, re_add, re_mul, re_rat, re_rat, re_inv, abs_mul, abs_inv, div_eq_mul_inv]
    by_cases hξ : ξ ∈ R
    · rw [Set.indicator_of_mem hξ]
      rw [e0, e1] at h1
      exact h1
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have h0 : (Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j) = 0 := by
        by_contra h
        exact hξ (h2 h)
      rw [h0, norm_zero]
  have hrew : ThR Φ t (gl (nU b * mD a) * k) =
      ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j := by
    unfold ThR
    rw [← (swapQ q hq).tsum_eq]
    refine tsum_congr fun ξ => ?_
    rw [row_eq, Yv_swap q hq b a a' ha' ξ]
  have hsn : Summable fun ξ : Rw ℚ => ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B0)
  rw [hrew]
  calc ‖∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖
      ≤ ∑' ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Rw ℚ, B0 * R.indicator Wt ξ := hsn.tsum_le_tsum hterm (hs.mul_left _)
    _ = B0 * ∑' ξ : Rw ℚ, R.indicator Wt ξ := tsum_mul_left
    _ ≤ B0 * (B1 * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) := mul_le_mul_of_nonneg_left hle hB0
    _ = B0 * B1 * (Bu / c) ^ (n + 2) * Real.exp (-((n : ℝ) * t)) * ab a ^ (n + 2) := by
        have : T = Bu / c * ab a := by rw [hT]; ring
        rw [this, mul_pow]
        ring
