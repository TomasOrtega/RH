import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationByDiscriminantMultipleStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Take `⟨C, B₁, hC⟩` from `hw`. Take `⟨C', hC', hB⟩` from `GlobalTheory.T.approximation_by_discriminant_multiple D.what₂.Tau Y.N Y.j Y.j_pos Y.j_lt`. Take `⟨h, hh1, hh2⟩` from `GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) hh`. Use `⟨C' * max C 0, max B₁ 2, fun B hBB => ?_⟩` and prove the remaining obligations. Establish `hB1 : B₁ ≤ B` using `le_trans (le_max_left _ _) hBB`.

Establish `hB2 : (2 : ℝ) ≤ B` using `by exact_mod_cast le_trans (le_max_right _ _) hBB`. Take `⟨P, hP1, hP2⟩` from `GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) (Φ B)`. Establish `hlog : 0 ≤ Real.log B / B` using `div_nonneg (Real.log_nonneg (by linarith)) (by linarith)`. Establish `hev : ∀ u : Wt Y, ev u (P - MvPolynomial.C Y.vol * h) = atWt Y (Φ B) u - Y.vol * atWt Y hh u`. Introduce `u`.

Establish `h1` using `hP2 u`. Establish `h2` using `hh2 u`. Simplify using `only [ev] at h1 h2 ⊢`. Rewrite using `[map_sub, map_mul, eval_C, h1, h2]`. Both sides reduce to the same expression.

Establish `hA : AntiL Y.j (P - MvPolynomial.C Y.vol * h)`. Introduce `τ a b hab hbj`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Establish `h1` using `hanti B hB2 τ a b hab hbj (fun σ i => x (σ, i))`.

Rewrite `h1` using `[← hev, ← hev]`. Rewrite using `[eval_rename, map_neg]`. Conclude with `h1`. Take `⟨al, be, E, hE1, hE2, hE3⟩` from `hB P h Y.vol (max C 0 * (Real.log B / B)) hvol (mul_nonneg (le_max_right _ _) hlog) hP1 hh1 hA (fun τ lam hd hg => by rw [hh2]; exact hfl.1 Y.j τ lam Y.j_pos Y.j_lt hd hg) (fun τ lam hl => by`. Rewrite using `[hP2]`.

Use `(hC B hB1 τ lam hl).trans ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)`. Use `⟨al, be, E, hE1, ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_assoc, mul_assoc]`.

Conclude with `hE2`. Use `hE3 u` as an intermediate fact. Rewrite `this` using `[hP2, hh2]`. Conclude with `this`.
-/
theorem shapeT_of_wallBd (D : D7) (Y : ShimX D.what₂.Tau) (Φ : ℝ → Fn Y) (hh : Fn Y) (hvol : 0 < Y.vol)
    (hanti : Antisym Φ hh) (hfl : FlagHt D.what₂.Tau Y.N hh) (hw : WallBd Φ) : ShapeT Φ hh := by
  obtain ⟨C, B₁, hC⟩ := hw
  obtain ⟨C', hC', hB⟩ := GlobalTheory.T.approximation_by_discriminant_multiple D.what₂.Tau Y.N Y.j Y.j_pos Y.j_lt
  obtain ⟨h, hh1, hh2⟩ := GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) hh
  refine ⟨C' * max C 0, max B₁ 2, fun B hBB => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hBB
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast le_trans (le_max_right _ _) hBB
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.FlagPoly.exists_form_of_functional D.what₂.Tau Y.N (dimFl D.what₂.Tau Y.N + 1) (Φ B)
  have hlog : 0 ≤ Real.log B / B := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hev : ∀ u : Wt Y, ev u (P - MvPolynomial.C Y.vol * h) = atWt Y (Φ B) u - Y.vol * atWt Y hh u := by
    intro u
    have h1 := hP2 u
    have h2 := hh2 u
    simp only [ev] at h1 h2 ⊢
    rw [map_sub, map_mul, eval_C, h1, h2]
    rfl
  have hA : AntiL Y.j (P - MvPolynomial.C Y.vol * h) := by
    intro τ a b hab hbj
    apply MvPolynomial.funext
    intro x
    have h1 := hanti B hB2 τ a b hab hbj (fun σ i => x (σ, i))
    rw [← hev, ← hev] at h1
    rw [eval_rename, map_neg]
    exact h1
  obtain ⟨al, be, E, hE1, hE2, hE3⟩ := hB P h Y.vol (max C 0 * (Real.log B / B)) hvol
    (mul_nonneg (le_max_right _ _) hlog) hP1 hh1 hA
    (fun τ lam hd hg => by rw [hh2]; exact hfl.1 Y.j τ lam Y.j_pos Y.j_lt hd hg)
    (fun τ lam hl => by
      rw [hP2]
      refine (hC B hB1 τ lam hl).trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  refine ⟨al, be, E, hE1, ?_, fun u => ?_⟩
  · rw [mul_div_assoc, mul_assoc]
    exact hE2
  · have := hE3 u
    rw [hP2, hh2] at this
    exact this

end GlobalTheory.Mean4
