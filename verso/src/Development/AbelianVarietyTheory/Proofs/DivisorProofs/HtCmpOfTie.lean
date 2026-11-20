import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

/- English proof (translation)
Take `⟨Cl, hCl⟩` from `hL`. Take `⟨t1, -, t3, t4, t5⟩` from `hT`. Use `choose s₀ hs₀ K hK using fun c => hF c (1 + ‖A.dir‖)`. Take `⟨K', hK'⟩` from `Finite.exists_le K`. Take `⟨M, hM⟩` from `Finite.exists_le fun c => (s₀ c)⁻¹`.

Use `set Λ : ℝ := 1 + ‖A.dir‖ with hΛ`. Establish `hΛ0 : 0 ≤ Λ` using `by positivity`. Use `set K₀ : ℝ := max K' 0 with hK₀`. Establish `hK0 : 0 ≤ K₀` using `le_max_right _ _`. Establish `hKK : ∀ c, K c ≤ K₀` using `fun c => (hK' c).trans (le_max_left _ _)`.

Establish `hM1 : (1 : ℝ) ≤ max M 1` using `le_max_right _ _`. Use `⟨(max M 1)⁻¹, by positivity, |Cl| * Λ + 2 * K₀, fun B hB u s hu hn hs hs' hd y => ?_⟩` and prove the remaining obligations. Establish `hs0 : (0 : ℝ) < s` using `by exact_mod_cast hs`. Establish `hs1 : (s : ℝ) ≤ 1` using `hs'.trans (inv_le_one_of_one_le₀ hM1)`. Establish `hsc : ∀ c, (s : ℝ) ≤ s₀ c` using `fun c => hs'.trans (inv_le_of_inv_le₀ (hs₀ c) ((hM c).trans (le_max_left _ _)))`.

Establish `hsh : A.sh u s = u - (s : ℝ) • A.dir` using `rfl`. Establish `hnorm : ‖A.sh u s‖ ≤ Λ`. Rewrite using `[hsh]`. Use `(norm_sub_le _ _).trans (add_le_add hn ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_of_nonneg hs0.le]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) hs1`. Establish `hfam` using `fun c => hK c (A.sh u s) hd hnorm s hs0 (hsc c)`. Establish `hsm : ∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)` using `fun c σ => (hfam c σ).1`. Take `⟨ta, tb⟩` from `t5 B hB`. Establish `hht` using `tb u s hu hs hd hsm y`.

Rewrite `hht` using `[map_add, map_add, map_smul, ← ta y, t1 B y _ (hsm _), smul_eq_mul]`. Establish `hlB : 1 / 2 ≤ Real.log B`. Use `Real.log_two_gt_d9` as an intermediate fact. Use `Real.log_le_log two_pos hB` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hls : 0 ≤ Real.log (1 / (s : ℝ))` using `Real.log_nonneg (one_le_one_div hs0 hs1)`. Establish `hdiv : Real.log (B / s) = Real.log B + Real.log (1 / (s : ℝ))`. Rewrite using `[div_eq_mul_one_div, Real.log_mul (by linarith) (by positivity)]`. Establish `hE : |P.ht B (Y.compPt y) y (T.L B _ (A.sh u s)) - H.h0 (A.sh u s) y| ≤ |Cl| * Λ * Real.log B` using `(hCl B hB _ y).trans (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hnorm (norm_nonneg _) (abs_nonneg _)) (by linarith))`. Take `⟨hE1, hE2⟩` from `abs_le.1 hE`.

Establish `hlo : -(K₀ * Real.log (1 / (s : ℝ))) - K₀ ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s)`. Rewrite using `[← P.mean_const (Y.compPt y) y (-(K₀ * Real.log (1 / (s : ℝ))) - K₀)]`. Use `P.mean_le fun σ i => le_trans ?_ ((hfam _ σ).2.2.2 _).1.1` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right (hKK (Y.compPt y)) hls` as an intermediate fact. Combine the linear relations using `[hKK (Y.compPt y)]`.

Establish `hup : P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) ≤ K₀`. Rewrite using `[← P.mean_const (Y.compPt y) y K₀]`. Conclude with `P.mean_le fun σ i => ((hfam _ σ).2.2.2 _).1.2.trans (hKK _)`. Establish `hKB : K₀ ≤ 2 * K₀ * Real.log B` using `by nlinarith`. Establish `h1 : 0 ≤ |Cl| * Λ * Real.log (1 / (s : ℝ))` using `by positivity`.

Establish `h2 : 0 ≤ K₀ * Real.log (1 / (s : ℝ))` using `by positivity`. Use `⟨?_, ?_, fun hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hht, hdiv]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hht]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hm : P.mean (Y.compPt y) y ((T.F _).ph (A.sh u s)) ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s)` using `P.mean_le fun σ i => (((hfam _ σ).2.2.2 _).2 ((t3 y).1 hy σ i)).1`. Rewrite using `[hht, t4 _ y hy]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem htCmp_of_tie (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y) (H : Ht Y) (P : T.Pts)
    (hF : ∀ c, (T.F c).FamS) (hT : HtTie A H P) (hL : LatCmp H P) : HtCmp A H := by
  obtain ⟨Cl, hCl⟩ := hL
  obtain ⟨t1, -, t3, t4, t5⟩ := hT
  choose s₀ hs₀ K hK using fun c => hF c (1 + ‖A.dir‖)
  obtain ⟨K', hK'⟩ := Finite.exists_le K
  obtain ⟨M, hM⟩ := Finite.exists_le fun c => (s₀ c)⁻¹
  set Λ : ℝ := 1 + ‖A.dir‖ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set K₀ : ℝ := max K' 0 with hK₀
  have hK0 : 0 ≤ K₀ := le_max_right _ _
  have hKK : ∀ c, K c ≤ K₀ := fun c => (hK' c).trans (le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  refine ⟨(max M 1)⁻¹, by positivity, |Cl| * Λ + 2 * K₀, fun B hB u s hu hn hs hs' hd y => ?_⟩
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (s : ℝ) ≤ 1 := hs'.trans (inv_le_one_of_one_le₀ hM1)
  have hsc : ∀ c, (s : ℝ) ≤ s₀ c := fun c =>
    hs'.trans (inv_le_of_inv_le₀ (hs₀ c) ((hM c).trans (le_max_left _ _)))
  have hsh : A.sh u s = u - (s : ℝ) • A.dir := rfl
  have hnorm : ‖A.sh u s‖ ≤ Λ := by
    rw [hsh]
    refine (norm_sub_le _ _).trans (add_le_add hn ?_)
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hs1
  have hfam := fun c => hK c (A.sh u s) hd hnorm s hs0 (hsc c)
  have hsm : ∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s) := fun c σ => (hfam c σ).1
  obtain ⟨ta, tb⟩ := t5 B hB
  have hht := tb u s hu hs hd hsm y
  rw [map_add, map_add, map_smul, ← ta y, t1 B y _ (hsm _), smul_eq_mul] at hht
  have hlB : 1 / 2 ≤ Real.log B := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log two_pos hB
    linarith
  have hls : 0 ≤ Real.log (1 / (s : ℝ)) := Real.log_nonneg (one_le_one_div hs0 hs1)
  have hdiv : Real.log (B / s) = Real.log B + Real.log (1 / (s : ℝ)) := by
    rw [div_eq_mul_one_div, Real.log_mul (by linarith) (by positivity)]
  have hE : |P.ht B (Y.compPt y) y (T.L B _ (A.sh u s)) - H.h0 (A.sh u s) y| ≤ |Cl| * Λ * Real.log B :=
    (hCl B hB _ y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (le_abs_self _) hnorm (norm_nonneg _) (abs_nonneg _)) (by linarith))
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hlo : -(K₀ * Real.log (1 / (s : ℝ))) - K₀ ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) := by
    rw [← P.mean_const (Y.compPt y) y (-(K₀ * Real.log (1 / (s : ℝ))) - K₀)]
    refine P.mean_le fun σ i => le_trans ?_ ((hfam _ σ).2.2.2 _).1.1
    have := mul_le_mul_of_nonneg_right (hKK (Y.compPt y)) hls
    linarith [hKK (Y.compPt y)]
  have hup : P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) ≤ K₀ := by
    rw [← P.mean_const (Y.compPt y) y K₀]
    exact P.mean_le fun σ i => ((hfam _ σ).2.2.2 _).1.2.trans (hKK _)
  have hKB : K₀ ≤ 2 * K₀ * Real.log B := by nlinarith
  have h1 : 0 ≤ |Cl| * Λ * Real.log (1 / (s : ℝ)) := by positivity
  have h2 : 0 ≤ K₀ * Real.log (1 / (s : ℝ)) := by positivity
  refine ⟨?_, ?_, fun hy => ?_⟩
  · rw [hht, hdiv]; nlinarith
  · rw [hht]; nlinarith
  · have hm : P.mean (Y.compPt y) y ((T.F _).ph (A.sh u s)) ≤ P.mean (Y.compPt y) y ((T.F _).phS (A.sh u s) s) :=
      P.mean_le fun σ i => (((hfam _ σ).2.2.2 _).2 ((t3 y).1 hy σ i)).1
    rw [hht, t4 _ y hy]; nlinarith

end GlobalTheory.Mean4O
