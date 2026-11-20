import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailBox
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailKernel
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourB
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

/- English proof (translation)
Take `⟨KB, hKB0, hKB⟩` from `tail_box_negLD δ hδ`. Take `⟨C₀, hC₀, hR⟩` from `Formalism.ZeroFreeDirichlet.l_log_deriv_right`. Use `⟨160 * KB + 32 * (1 + C₀), by positivity, ?_⟩` and prove the remaining obligations. Introduce `N _ χ Q z η hχ hQ hNQ hbox hz hη hη1`. Establish `hbox' : ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 → ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ KB * Real.log Q` using `hKB N χ Q hχ hQ hNQ hbox`.

Use `set σ₁ : ℝ := 1 - 1 / 400 + δ with hσ₁`. Use `set T : ℝ := Q / 2 with hTdef`. Use `set Lq : ℝ := Real.log Q with hLq`. Establish `hT0 : 0 < T` using `by rw [hTdef]; linarith`. Establish `hTQ : T ≤ Q - 1` using `by rw [hTdef]; linarith`.

Establish `hσa : 0 < σ₁` using `by rw [hσ₁]; linarith`. Establish `hσb : σ₁ < 1` using `by rw [hσ₁]; linarith`. Establish `hσc : 1 / 2 ≤ σ₁` using `by rw [hσ₁]; linarith`. Establish `hσd : σ₁ ≤ 1 - 1 / 800` using `by rw [hσ₁]; linarith`. Establish `hLq2 : 1 / 2 ≤ Lq`.

Use `Real.log_le_log (by norm_num) hQ` as an intermediate fact. Combine the linear relations using `[Real.log_two_gt_d9]`. Establish `hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0` using `fun w h1 _ h3 => hbox w (by rw [hσ₁] at h1; linarith) (by linarith)`. Establish `hz0 : 0 < z` using `by linarith`. Use `set y1 : ℝ := z + z * η with hy1def`.

Establish `hy1 : 1 ≤ y1` using `by rw [hy1def]; nlinarith`. Establish `hy12 : y1 ≤ 2 * z` using `by rw [hy1def]; nlinarith`. Establish `I1` using `tail_shift_identity χ hχ y1 σ₁ T hy1 hσa hσb hT0 hzf`. Establish `I0` using `tail_shift_identity χ hχ z σ₁ T hz hσa hσb hT0 hzf`. Establish `key : (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) = (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.negLD χ 1 * y1) - (2 * R …`.

Rewrite using `[hy1def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[I1, I0]`. Establish `hcomb` using `(congrArg norm key).le.trans (tc_norm_comb _ _ _ _ _ _ _ _)`.

Establish `hE : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ‖∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 2 * Real.pi * (8 * (1 + C₀) * (z ^ 2 / Q))`. Introduce `y hy hy2`. Establish `h` using `Formalism.ZF.norm_integral_compl_le (fun t => Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)) ((1 + C₀) * (4 * z ^ 2)) T (by positivity) hT0 (fun t ht => by`. Establish `ht0 : t ≠ 0` using `by intro h0; rw [h0, abs_zero] at ht; linarith`. Use `(tc_right_pt χ C₀ (fun s hs => hR N χ s hs) y t (by linarith) ht0).trans ?_` and prove the remaining obligations.

Establish `hyy : y ^ 2 ≤ 4 * z ^ 2` using `by nlinarith`. Use the proof step `gcongr)`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hTdef]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hH : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ∀ v : ℝ, |v| = T → ‖∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ 16 * KB * Lq * (z ^ 2 / Q)`. Introduce `y hy hy2 v hv`. Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)) (C := KB * Lq * (4 * z ^ 2) / T ^ 2) (a := σ₁) (b := 2) (fun x hx => by`. Rewrite `hx` using `[Set.uIoc_of_le (by linarith)]`.

Establish `hM` using `hbox' ((x : ℂ) + (v : ℂ) * I) (by simp; exact hx.1.le) (by simp; rw [hv]; exact hTQ)`. Use `(tc_horiz_pt χ _ y T x v hy hT0 hv hx.2 hM).trans ?_` and prove the remaining obligations. Establish `hyy : y ^ 2 ≤ 4 * z ^ 2` using `by nlinarith`. Establish `hM0 : 0 ≤ KB * Real.log Q` using `le_trans (norm_nonneg _) hM`. Use the proof step `gcongr)`.

Use `h.trans ?_` and prove the remaining obligations. Establish `hlen : |2 - σ₁| ≤ 2` using `by rw [abs_of_pos (by linarith)]; linarith`. Establish `hKL : 0 ≤ KB * Lq` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hV` using `tc_left_int χ hχ z η σ₁ T (KB * Lq) hz0 hη.le hη1 hσc hσd hT0.le (fun u hu => hzf _ (by simp) (by simp; linarith) (by simpa using hu)) (fun u hu => hbox' _ (by simp) (by simpa using hu.trans hTQ))`.

Rewrite `hV` using `[← hy1def]`. Establish `hlog : Real.log (1 + 800 * T) ≤ 10 * Lq` using `by rw [hTdef, hLq]; exact tc_log_bound Q hQ`. Establish `hLq0 : 0 ≤ Lq` using `by linarith`. Use `set A : ℝ := z ^ 2 / Q with hAdef`. Use `set Bv : ℝ := η * z ^ σ₁ with hBvdef`.

Establish `hA0 : 0 ≤ A` using `div_nonneg (sq_nonneg z) (by linarith)`. Establish `hB0 : 0 ≤ Bv` using `mul_nonneg hη.le (Real.rpow_nonneg hz0.le _)`. Establish `hV' : ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y1 ((σ₁ : ℂ) + (u : ℂ) * I)) - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ₁ : ℂ) + (u : ℂ) * I)‖ ≤ 160 * KB * Lq ^ 2 * Bv`. Use `hV.trans ?_` and prove the remaining obligations. Establish `hn : 0 ≤ KB * Lq * (4 * η * z ^ σ₁)` using `mul_nonneg (mul_nonneg hKB0 hLq0) (mul_nonneg (by linarith) (Real.rpow_nonneg hz0.le _))`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hn` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 160 * KB * Lq ^ 2 * Bv := by rw [hBvdef]; ring`. Establish `hE1` using `hE y1 hy1 hy12`.

Establish `hE0` using `hE z hz (by linarith)`. Establish `hHa1` using `hH y1 hy1 hy12 (-T) (by rw [abs_neg, abs_of_pos hT0])`. Establish `hHb1` using `hH y1 hy1 hy12 T (abs_of_pos hT0)`. Establish `hHa0` using `hH z hz (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT0])`. Establish `hHb0` using `hH z hz (by linarith) T (abs_of_pos hT0)`.

Establish `hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi`. Rewrite using `[show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Rewrite `hcomb` using `[norm_mul, hn]`. Use `set X := ‖Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ with hXdef`. Establish `hpi : 1 ≤ 2 * Real.pi` using `by linarith [Real.pi_gt_three]`.

Establish `hW : 0 ≤ 64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv`. Use `mul_nonneg (mul_nonneg hKB0 hLq0) hA0` as an intermediate fact. Use `mul_nonneg (mul_nonneg hKB0 (sq_nonneg Lq)) hB0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hWW` using `le_mul_of_one_le_left hW hpi`.

Establish `h2X : 2 * Real.pi * X ≤ 2 * Real.pi * (16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hXR : X ≤ 16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv)` using `le_of_mul_le_mul_left h2X (by positivity)`. Establish `p1 : 0 ≤ KB * Lq * A` using `mul_nonneg (mul_nonneg hKB0 hLq0) hA0`. Establish `p2 : 0 ≤ (1 + C₀) * Lq ^ 2 * Bv` using `mul_nonneg (mul_nonneg (by linarith) (sq_nonneg Lq)) hB0`.

Establish `p3 : 0 ≤ (1 + C₀) * A * (2 * Lq - 1)` using `mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)`. Establish `hgoal : (160 * KB + 32 * (1 + C₀)) * Lq * (Lq * η * z ^ σ₁ + A) = 160 * KB * Lq ^ 2 * Bv + 160 * KB * Lq * A + 32 * (1 + C₀) * Lq ^ 2 * Bv + 32 * (1 + C₀) * Lq * A` using `by rw [hBvdef]; ring`. Rewrite using `[hgoal]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tail_contour (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 800) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q z η : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ → 1 ≤ z → 0 < η → η ≤ 1 →
      ‖Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ ≤
        K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + δ) + z ^ 2 / Q) := by
  obtain ⟨KB, hKB0, hKB⟩ := tail_box_negLD δ hδ
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  refine ⟨160 * KB + 32 * (1 + C₀), by positivity, ?_⟩
  intro N _ χ Q z η hχ hQ hNQ hbox hz hη hη1
  have hbox' : ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ KB * Real.log Q := hKB N χ Q hχ hQ hNQ hbox
  set σ₁ : ℝ := 1 - 1 / 400 + δ with hσ₁
  set T : ℝ := Q / 2 with hTdef
  set Lq : ℝ := Real.log Q with hLq
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hTQ : T ≤ Q - 1 := by rw [hTdef]; linarith
  have hσa : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσb : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσc : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσd : σ₁ ≤ 1 - 1 / 800 := by rw [hσ₁]; linarith
  have hLq2 : 1 / 2 ≤ Lq := by
    have := Real.log_le_log (by norm_num) hQ
    linarith [Real.log_two_gt_d9]
  have hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w ≠ 0 := fun w h1 _ h3 =>
    hbox w (by rw [hσ₁] at h1; linarith) (by linarith)
  have hz0 : 0 < z := by linarith
  set y1 : ℝ := z + z * η with hy1def
  have hy1 : 1 ≤ y1 := by rw [hy1def]; nlinarith
  have hy12 : y1 ≤ 2 * z := by rw [hy1def]; nlinarith
  have I1 := tail_shift_identity χ hχ y1 σ₁ T hy1 hσa hσb hT0 hzf
  have I0 := tail_shift_identity χ hχ z σ₁ T hz hσa hσb hT0 hzf
  have key : (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1)
      = (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.negLD χ 1 * y1)
        - (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ z - Formalism.ZeroFreeDirichlet.negLD χ 1 * z) := by
    rw [hy1def]; push_cast; ring
  rw [I1, I0] at key
  have hcomb := (congrArg norm key).le.trans (tc_norm_comb _ _ _ _ _ _ _ _)

  have hE : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z →
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        2 * Real.pi * (8 * (1 + C₀) * (z ^ 2 / Q)) := by
    intro y hy hy2
    have h := Formalism.ZF.norm_integral_compl_le (fun t => Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      ((1 + C₀) * (4 * z ^ 2)) T (by positivity) hT0 (fun t ht => by
        have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
        refine (tc_right_pt χ C₀ (fun s hs => hR N χ s hs) y t (by linarith) ht0).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        gcongr)
    refine h.trans (le_of_eq ?_)
    rw [hTdef]; field_simp; ring

  have hH : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ∀ v : ℝ, |v| = T →
      ‖∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ 16 * KB * Lq * (z ^ 2 / Q) := by
    intro y hy hy2 v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := KB * Lq * (4 * z ^ 2) / T ^ 2) (a := σ₁) (b := 2) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hM := hbox' ((x : ℂ) + (v : ℂ) * I) (by simp; exact hx.1.le)
          (by simp; rw [hv]; exact hTQ)
        refine (tc_horiz_pt χ _ y T x v hy hT0 hv hx.2 hM).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        have hM0 : 0 ≤ KB * Real.log Q := le_trans (norm_nonneg _) hM
        gcongr)
    refine h.trans ?_
    have hlen : |2 - σ₁| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
    have hKL : 0 ≤ KB * Lq := by positivity
    calc KB * Lq * (4 * z ^ 2) / T ^ 2 * |2 - σ₁| ≤ KB * Lq * (4 * z ^ 2) / T ^ 2 * 2 := by gcongr
      _ = 32 * (KB * Lq) * (z ^ 2 / Q) / Q := by rw [hTdef]; field_simp; ring
      _ ≤ 32 * (KB * Lq) * (z ^ 2 / Q) / 2 := by gcongr
      _ = 16 * KB * Lq * (z ^ 2 / Q) := by ring

  have hV := tc_left_int χ hχ z η σ₁ T (KB * Lq) hz0 hη.le hη1 hσc hσd hT0.le
    (fun u hu => hzf _ (by simp) (by simp; linarith) (by simpa using hu))
    (fun u hu => hbox' _ (by simp) (by simpa using hu.trans hTQ))
  rw [← hy1def] at hV
  have hlog : Real.log (1 + 800 * T) ≤ 10 * Lq := by rw [hTdef, hLq]; exact tc_log_bound Q hQ
  have hLq0 : 0 ≤ Lq := by linarith
  set A : ℝ := z ^ 2 / Q with hAdef
  set Bv : ℝ := η * z ^ σ₁ with hBvdef
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg z) (by linarith)
  have hB0 : 0 ≤ Bv := mul_nonneg hη.le (Real.rpow_nonneg hz0.le _)
  have hV' : ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y1 ((σ₁ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ₁ : ℂ) + (u : ℂ) * I)‖ ≤ 160 * KB * Lq ^ 2 * Bv := by
    refine hV.trans ?_
    have hn : 0 ≤ KB * Lq * (4 * η * z ^ σ₁) :=
      mul_nonneg (mul_nonneg hKB0 hLq0) (mul_nonneg (by linarith) (Real.rpow_nonneg hz0.le _))
    calc KB * Lq * (4 * η * z ^ σ₁) * (4 * Real.log (1 + 800 * T))
        ≤ KB * Lq * (4 * η * z ^ σ₁) * (4 * (10 * Lq)) := by
          apply mul_le_mul_of_nonneg_left _ hn; linarith
      _ = 160 * KB * Lq ^ 2 * Bv := by rw [hBvdef]; ring
  have hE1 := hE y1 hy1 hy12
  have hE0 := hE z hz (by linarith)
  have hHa1 := hH y1 hy1 hy12 (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb1 := hH y1 hy1 hy12 T (abs_of_pos hT0)
  have hHa0 := hH z hz (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb0 := hH z hz (by linarith) T (abs_of_pos hT0)
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hn] at hcomb
  set X := ‖Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ with hXdef
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hW : 0 ≤ 64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv := by
    have := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
    have := mul_nonneg (mul_nonneg hKB0 (sq_nonneg Lq)) hB0
    linarith
  have hWW := le_mul_of_one_le_left hW hpi
  have h2X : 2 * Real.pi * X ≤
      2 * Real.pi * (16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv)) := by
    linarith
  have hXR : X ≤ 16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv) :=
    le_of_mul_le_mul_left h2X (by positivity)
  have p1 : 0 ≤ KB * Lq * A := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
  have p2 : 0 ≤ (1 + C₀) * Lq ^ 2 * Bv := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg Lq)) hB0
  have p3 : 0 ≤ (1 + C₀) * A * (2 * Lq - 1) := mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)
  have hgoal : (160 * KB + 32 * (1 + C₀)) * Lq * (Lq * η * z ^ σ₁ + A) =
      160 * KB * Lq ^ 2 * Bv + 160 * KB * Lq * A + 32 * (1 + C₀) * Lq ^ 2 * Bv
        + 32 * (1 + C₀) * Lq * A := by rw [hBvdef]; ring
  rw [hgoal]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
