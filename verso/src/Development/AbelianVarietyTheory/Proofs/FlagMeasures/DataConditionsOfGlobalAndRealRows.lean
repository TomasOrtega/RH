import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisonsStatement

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

/- English proof (translation)
Take `⟨x1, hx1⟩` from `GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos`. Use `⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩` and prove the remaining obligations. Establish `hxx1 : x1 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hxone : 1 ≤ x` using `le_trans (le_max_right _ _) hx`. Take `⟨-, -, -, h12, -⟩` from `hx1 x hxx1 _ _ _ _ _ hG.nums`.

Establish `hk : 5 ≤ D.R.k`. Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hm2` using `D.R.two_le_m`.

Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b → g ⟨a, ha⟩ = g ⟨b, hb⟩`. Introduce `n g a b ha hb h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Establish `huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k), Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ)`. Introduce `u τ i h1 h2`. Unfold `Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS`. Rewrite using `[dif_pos ⟨h1, h2⟩]`. Establish `hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1), Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ)`.

Introduce `τ l h1 h2`. Unfold `Formalism.MainNotions.S.vOne`. Rewrite using `[dif_pos ⟨h1, h2⟩]`. Establish `hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ`. Introduce `τ`.

Unfold `Formalism.MainNotions.S.bOne bFirst`. Rewrite using `[dif_pos ⟨le_rfl, by have := D.R.two_le_m; omega⟩]`. Establish `hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ`. Introduce `u τ`. Rewrite using `[huO u τ 1 le_rfl (by omega)]`.

Unfold `uFirst`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))`. Establish `huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ`. Introduce `u τ`. Rewrite using `[huO u τ D.R.k (by omega) le_rfl]`.

Unfold `uLast`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))`. Establish `hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ`. Introduce `τ`. Rewrite using `[hvO τ 1 le_rfl (by omega)]`.

Unfold `vFirst`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))`. Establish `hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ`. Introduce `τ`. Rewrite using `[hvO τ (D.R.k - 1) (by omega) le_rfl]`.

Unfold `vLast`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))`. Establish `hDel : (0 : ℝ) < D.s.Del` using `by exact_mod_cast D.s.Del_pos`. Establish `hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del` using `mul_nonneg (Nat.cast_nonneg _) hDel.le`. Establish `hbx : 1 ≤ bx x eps`.

Unfold `bx`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (by linarith) _)`. Establish `hg : ∀ i, 2 ≤ D.host.g i`. Introduce `i`. Establish `h` using `(hG.g_win i).1`.

Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps` using `by nlinarith`. Establish `h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h2.trans h` after adjusting the coercions.

Unfold `Formalism.MainNotions.S.StandingNumericalData`. Simplify using `only`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩` and prove the remaining obligations. Introduce `τ l h1 h2`. Rewrite using `[hvO τ l h1 h2]`.

Conclude with `hG.cloud τ ⟨l - 1, by omega⟩`. Introduce `u l h1 h2`. Establish `key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 - (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0)`. Introduce `τ`. Rewrite using `[huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]`.

Establish `e` using `D.s.u_letter u τ (l - 1) (by omega)`. Rewrite `e` using `[D.hcW_v u τ]`. Establish `e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩` using `hF _ _ _ _ _ (by omega)`. Rewrite using `[e', e]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.

Distinguish the cases in `hL : D.s.letter u ⟨l - 1, by omega⟩ = true`. Use `right`. Introduce `τ`. Rewrite using `[key τ, if_pos hL]`. Use `left`.

Introduce `τ`. Rewrite using `[key τ, if_neg hL]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u τ`. Rewrite using `[hu1 u τ, hv1 τ]`.

Distinguish the cases in `ht : Top D τ`. Establish `h1` using `(hN.top τ ht).1`. Establish `h2` using `(hG.cloud τ ⟨0, by omega⟩).2`. Establish `hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ)`. Unfold `vFirst`.

Both sides reduce to the same expression. Rewrite using `[hvF]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(hG.off τ ht).1`. Introduce `u τ ht`.

Rewrite using `[hu1 u τ, hv1 τ]`. Conclude with `(hG.off τ ht).2.1`. Introduce `u τ ht`. Rewrite using `[huk u τ, hvk τ]`. Conclude with `(hG.off τ ht).2.2`.

Introduce `τ ht`. Unfold `Formalism.MainNotions.S.bTop`. Rewrite using `[huk D.u₀ τ, hbO τ]`. Take `⟨-, -, h3, h4⟩` from `hN.top τ ht`. Apply the tactic sequence `constructor <;> linarith`.

Introduce `u τ`. Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Establish `hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ)`. Unfold `Formalism.MainNotions.S.lamS`.

Rewrite using `[dif_pos (show i < D.R.k - 1 by omega), D.hcW_v u τ]`. Rewrite using `[hl]`. Unfold `Formalism.MainNotions.S.uS`. Conclude with `⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩, by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩`. Introduce `h`.

Establish `hm : 0 < D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ = -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ)`. Unfold `Formalism.MainNotions.S.lamS`.

Rewrite using `[dif_neg (show ¬ (D.R.k - 1 < D.R.k - 1) by omega), dif_pos (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]`. Conclude with `congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))`. Rewrite using `[hl]`. Unfold `Formalism.MainNotions.S.uS`. Conclude with `(D.hcW u τ).u_last_gt h hm` after adjusting the coercions.

Introduce `u u' hne τ heq`. Establish `hl : D.s.letter u ≠ D.s.letter u'` using `fun h => hne (D.s.letter_inj h)`. Take `⟨⟨j, hj⟩, hjl⟩` from `Function.ne_iff.mp hl`. Establish `e` using `congrFun heq ⟨j + 1, by omega⟩`. Simplify using `only [Formalism.MainNotions.S.uS] at e`.

Establish `e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩`. Conclude with `e` after adjusting the coercions. Rewrite `e'` using `[D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v]`. Establish `hQ` using `D.s.Del_pos`. Apply the tactic sequence `cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>`.

Apply the tactic sequence `simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith`. Introduce `u`. Conclude with `⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩`. Introduce `u`. Conclude with `Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)`.
-/
theorem data_of_rows (eps CD : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hCD : 3 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D →
      DuWin D C0 → StandingNumericalData D C0 := by
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos
  refine ⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨-, -, -, h12, -⟩ := hx1 x hxx1 _ _ _ _ _ hG.nums
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl

  have hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
    intro n g a b ha hb h
    subst h
    rfl

  have huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k),
      Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by
    intro u τ i h1 h2
    unfold Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS
    rw [dif_pos ⟨h1, h2⟩]
  have hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1),
      Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ) := by
    intro τ l h1 h2
    unfold Formalism.MainNotions.S.vOne
    rw [dif_pos ⟨h1, h2⟩]
  have hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ := by
    intro τ
    unfold Formalism.MainNotions.S.bOne bFirst
    rw [dif_pos ⟨le_rfl, by have := D.R.two_le_m; omega⟩]
  have hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ := by
    intro u τ
    rw [huO u τ 1 le_rfl (by omega)]
    unfold uFirst
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))
  have huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ := by
    intro u τ
    rw [huO u τ D.R.k (by omega) le_rfl]
    unfold uLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))
  have hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ := by
    intro τ
    rw [hvO τ 1 le_rfl (by omega)]
    unfold vFirst
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))
  have hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ := by
    intro τ
    rw [hvO τ (D.R.k - 1) (by omega) le_rfl]
    unfold vLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del := mul_nonneg (Nat.cast_nonneg _) hDel.le

  have hbx : 1 ≤ bx x eps := by
    unfold bx
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hg : ∀ i, 2 ≤ D.host.g i := by
    intro i
    have h := (hG.g_win i).1
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps := by nlinarith
    have h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 :=
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.k : ℝ) * bx x eps := h5
        _ ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast h2.trans h
  unfold Formalism.MainNotions.S.StandingNumericalData
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  ·
    intro τ l h1 h2
    rw [hvO τ l h1 h2]
    exact hG.cloud τ ⟨l - 1, by omega⟩
  ·
    intro u l h1 h2
    have key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 -
        (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0) := by
      intro τ
      rw [huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]
      have e := D.s.u_letter u τ (l - 1) (by omega)
      rw [D.hcW_v u τ] at e
      have e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩ :=
        hF _ _ _ _ _ (by omega)
      rw [e', e]
      split_ifs <;> push_cast <;> ring
    by_cases hL : D.s.letter u ⟨l - 1, by omega⟩ = true
    · right
      intro τ
      rw [key τ, if_pos hL]
    · left
      intro τ
      rw [key τ, if_neg hL]
      ring
  ·
    intro u τ
    rw [hu1 u τ, hv1 τ]
    by_cases ht : Top D τ
    · have h1 := (hN.top τ ht).1
      have h2 := (hG.cloud τ ⟨0, by omega⟩).2
      have hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
        unfold vFirst
        rfl
      rw [hvF]
      nlinarith
    · exact (hG.off τ ht).1
  ·
    intro u τ ht
    rw [hu1 u τ, hv1 τ]
    exact (hG.off τ ht).2.1
  ·
    intro u τ ht
    rw [huk u τ, hvk τ]
    exact (hG.off τ ht).2.2
  ·
    intro τ ht
    unfold Formalism.MainNotions.S.bTop
    rw [huk D.u₀ τ, hbO τ]
    obtain ⟨-, -, h3, h4⟩ := hN.top τ ht
    constructor <;> linarith
  ·
    intro u τ
    constructor
    · intro i hi
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dif_pos (show i < D.R.k - 1 by omega), D.hcW_v u τ]
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact ⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩,
        by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩
    · intro h
      have hm : 0 < D.R.m := by
        have := D.R.two_le_m
        omega
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ =
          -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dif_neg (show ¬ (D.R.k - 1 < D.R.k - 1) by omega),
          dif_pos (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]
        exact congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact_mod_cast (D.hcW u τ).u_last_gt h hm
  ·
    intro u u' hne τ heq
    have hl : D.s.letter u ≠ D.s.letter u' := fun h => hne (D.s.letter_inj h)
    obtain ⟨⟨j, hj⟩, hjl⟩ := Function.ne_iff.mp hl
    have e := congrFun heq ⟨j + 1, by omega⟩
    simp only [Formalism.MainNotions.S.uS] at e
    have e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩ := by
      exact_mod_cast e
    rw [D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v] at e'
    have hQ := D.s.Del_pos
    cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>
      simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith
  ·
    intro u
    exact ⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩
  ·
    intro u
    exact Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)

end GlobalTheory.Diag.PG

end
