import ReciprocityTheory.SemistableReduction.ShareBallC

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

/- English proof (translation)
Introduce `r p H s hH hJ hs0 hs1 hP u`. Establish `hHh : Hᴴ = H` using `hH.isHermitian`. Establish `hsurj` using `sb_setup hH hJ hP`. Establish `hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v` using `fun v => by`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]`. Establish `hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x` using `fun x hx => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mulVec_mulVec, sb_J_mul_J, one_mulVec]`.

Use `_ = _ := by rw [hx]`. Establish `hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y)` using `fun y hy => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mulVec_mulVec, sb_J_mul_J, one_mulVec]`. Use `_ = _ := by rw [hy, mulVec_neg]`.

Establish `horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y → star x ⬝ᵥ (signMat p r *ᵥ y) = 0`. Introduce `x y hx hy`. Establish `e` using `sb_herm_swap hHh x y`. Rewrite `e` using `[hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)]`. Take the linear combination `(-1 / 2 : ℂ) * e`.

Establish `horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y → star y ⬝ᵥ (signMat p r *ᵥ x) = 0`. Introduce `x y hx hy`. Establish `e` using `sb_herm_swap hHh y x`. Rewrite `e` using `[hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)]`. Take the linear combination `(1 / 2 : ℂ) * e`.

Establish `hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y`. Introduce `y hy`. Take `⟨x, hx, hxy⟩` from `hsurj y`. Establish `o` using `horth x y hx hy`. Rewrite `o` using `[sb_dot_J, sub_eq_zero, hxy]`.

Establish `hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re`. Rewrite using `[← o, sb_re_star_dot, sb_posSq_eq]`. Establish `cs` using `sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)`. Rewrite `cs` using `[← hA, ← sb_negSq_eq, ← sb_negSq_eq]`. Establish `hx'` using `hP x hx`.

Establish `hpx : posSq p x = posSq p y` using `by rw [sb_posSq_eq, sb_posSq_eq, hxy]`. Establish `hA0 : 0 ≤ posSq p y` using `by rw [sb_posSq_eq]; exact sb_normSq_nonneg _`. Establish `hD0 : 0 ≤ negSq p y` using `by rw [sb_negSq_eq]; exact sb_normSq_nonneg _`. Rewrite `hx'` using `[hpx]`. Break down `hA0.eq_or_lt with h | h` into its components or cases.

Rewrite using `[← h]`. Check the signs of the components of the expression. Establish `h2` using `mul_le_mul_of_nonneg_right hx' hD0`. Conclude with `le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤ posSq p y * (s ^ 2 * negSq p y)) h`. Establish `hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u` using `⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)), by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm], by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub], by ext k; simp; ring⟩`.

Take `⟨x, y, hx, hy, rfl⟩` from `hdec`. Establish `hPx` using `hP x hx`. Establish `hPy` using `hNprop y hy`. Use `set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef`. Establish `ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t`.

Establish `o` using `horth x y hx hy`. Rewrite `o` using `[sb_dot_J, sub_eq_zero]`. Rewrite using `[htdef, o]`. Establish `hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y`. Establish `e1` using `sb_re_dot_J p x`.

Establish `e2` using `sb_re_dot_J p y`. Rewrite using `[hq, mulVec_add, hHx x hx, hHy y hy, star_add]`. Simplify using `only [add_dotProduct, dotProduct_add, dotProduct_neg]`. Rewrite using `[horth x y hx hy, horth' x y hx hy]`. Simplify using `only [Complex.add_re, Complex.neg_re, Complex.zero_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn_eq : normSq (x + y) = posSq p x + negSq p x + posSq p y + negSq p y + 4 * t`. Establish `a3 : (star x ⬝ᵥ y).re = 2 * t` using `by rw [sb_dot_split p, Complex.add_re, ht2]; ring`. Establish `a4 : (star y ⬝ᵥ x).re = 2 * t` using `by rw [sb_re_dot_comm, a3]`. Rewrite using `[← sb_re_star_dot, star_add]`.

Simplify using `only [add_dotProduct, dotProduct_add, Complex.add_re]`. Rewrite using `[a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA0 : 0 ≤ posSq p x` using `by rw [sb_posSq_eq]; exact sb_normSq_nonneg _`. Establish `hB0 : 0 ≤ negSq p x` using `by rw [sb_negSq_eq]; exact sb_normSq_nonneg _`.

Establish `hC0 : 0 ≤ posSq p y` using `by rw [sb_posSq_eq]; exact sb_normSq_nonneg _`. Establish `hD0 : 0 ≤ negSq p y` using `by rw [sb_negSq_eq]; exact sb_normSq_nonneg _`. Establish `hts1 : t ^ 2 ≤ posSq p x * posSq p y`. Rewrite using `[sb_posSq_eq, sb_posSq_eq]`. Conclude with `sb_cs _ _`.

Establish `hts2 : t ^ 2 ≤ negSq p x * negSq p y`. Rewrite using `[← ht2, sb_negSq_eq, sb_negSq_eq]`. Conclude with `sb_cs _ _`. Establish `hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z` using `fun z hz => by`. Rewrite using `[Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]`.

Establish `hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x)` using `(Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))`. Establish `hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y)` using `(Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))`. Establish `h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y)`. Rewrite using `[← Real.sqrt_mul hA0]`. Conclude with `Real.abs_le_sqrt hts1`.

Establish `h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y)`. Rewrite using `[← Real.sqrt_mul hB0]`. Conclude with `Real.abs_le_sqrt hts2`. Take `⟨hU, hL⟩` from `sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2`. Rewrite `hU`, `hL` using `[Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0]`.

Establish `h1s : 0 < 1 - s` using `by linarith`. Rewrite using `[hq_eq, hn_eq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ h1s]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ h1s]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem boundedBall_holds : BoundedBallStatement := by
  intro r p H s hH hJ hs0 hs1 hP u
  have hHh : Hᴴ = H := hH.isHermitian
  have hsurj := sb_setup hH hJ hP
  have hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]
  have hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x := fun x hx => by
    calc H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hx]
  have hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y) := fun y hy => by
    calc H *ᵥ y = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ y)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hy, mulVec_neg]
  have horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star x ⬝ᵥ (signMat p r *ᵥ y) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh x y
    rw [hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (-1 / 2 : ℂ) * e
  have horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star y ⬝ᵥ (signMat p r *ᵥ x) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh y x
    rw [hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (1 / 2 : ℂ) * e
  have hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero, hxy] at o
    have hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re := by
      rw [← o, sb_re_star_dot, sb_posSq_eq]
    have cs := sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)
    rw [← hA, ← sb_negSq_eq, ← sb_negSq_eq] at cs
    have hx' := hP x hx
    have hpx : posSq p x = posSq p y := by rw [sb_posSq_eq, sb_posSq_eq, hxy]
    have hA0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
    have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
    rw [hpx] at hx'
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have h2 := mul_le_mul_of_nonneg_right hx' hD0
      exact le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤
        posSq p y * (s ^ 2 * negSq p y)) h
  have hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u :=
    ⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)),
      by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm],
      by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub],
      by ext k; simp; ring⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := hdec
  have hPx := hP x hx
  have hPy := hNprop y hy
  set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef
  have ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t := by
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero] at o
    rw [htdef, o]
  have hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y := by
    have e1 := sb_re_dot_J p x
    have e2 := sb_re_dot_J p y
    rw [hq, mulVec_add, hHx x hx, hHy y hy, star_add]
    simp only [add_dotProduct, dotProduct_add, dotProduct_neg]
    rw [horth x y hx hy, horth' x y hx hy]
    simp only [Complex.add_re, Complex.neg_re, Complex.zero_re]
    linarith
  have hn_eq : normSq (x + y) =
      posSq p x + negSq p x + posSq p y + negSq p y + 4 * t := by
    have a3 : (star x ⬝ᵥ y).re = 2 * t := by rw [sb_dot_split p, Complex.add_re, ht2]; ring
    have a4 : (star y ⬝ᵥ x).re = 2 * t := by rw [sb_re_dot_comm, a3]
    rw [← sb_re_star_dot, star_add]
    simp only [add_dotProduct, dotProduct_add, Complex.add_re]
    rw [a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]
    ring
  have hA0 : 0 ≤ posSq p x := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hB0 : 0 ≤ negSq p x := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hC0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hts1 : t ^ 2 ≤ posSq p x * posSq p y := by
    rw [sb_posSq_eq, sb_posSq_eq]; exact sb_cs _ _
  have hts2 : t ^ 2 ≤ negSq p x * negSq p y := by
    rw [← ht2, sb_negSq_eq, sb_negSq_eq]; exact sb_cs _ _
  have hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z := fun z hz => by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
  have hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x) :=
    (Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))
  have hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y) :=
    (Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))
  have h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y) := by
    rw [← Real.sqrt_mul hA0]; exact Real.abs_le_sqrt hts1
  have h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y) := by
    rw [← Real.sqrt_mul hB0]; exact Real.abs_le_sqrt hts2
  obtain ⟨hU, hL⟩ := sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0] at hU hL
  have h1s : 0 < 1 - s := by linarith
  rw [hq_eq, hn_eq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith

end ReciprocityTheory.MultiplicativeHeights
