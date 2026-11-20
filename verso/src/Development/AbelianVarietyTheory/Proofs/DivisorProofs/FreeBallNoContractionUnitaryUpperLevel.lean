import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProofStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.FreeBallAt

open GlobalTheory.Up GlobalTheory.Up.BallExPf
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Introduce `N hN hop`. Use `h N hN fun τ => ?_` and prove the remaining obligations. Take `⟨c, hc0, hc1, hc⟩` from `hop τ`. Use `⟨c, hc0, hc1, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, GlobalTheory.MajInv.maj_rmul X.toData hx1 hb]`.

Conclude with `hc u`.
-/
theorem noContraction_of_rmul (X : DataX E r) {x1 b : Frame X.Ψ r} (hx1 : x1 ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) (h : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X (rmul x1 b)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x1 := by
  intro N hN hop
  refine h N hN fun τ => ?_
  obtain ⟨c, hc0, hc1, hc⟩ := hop τ
  refine ⟨c, hc0, hc1, fun u => ?_⟩
  rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, GlobalTheory.MajInv.maj_rmul X.toData hx1 hb]
  exact hc u

/- English proof (translation)
Introduce `u`. Rewrite using `[ModeHalfA.maj_orth X h0, ModeHalfA.maj_orth X h0]`. Express the relevant statement in the definitionally equal form `ReciprocityTheory.MultiplicativeHeights.normSq _ ≤ _ * ReciprocityTheory.MultiplicativeHeights.normSq _`. Establish `hk` using `ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg hr`. Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)`.

Establish `hu1 : IsUnit (mat z1 τ).det` using `isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X z1 h1 τ)`. Establish `b1` using `(frame_bound hr X h0 h1 hlt τ ((mat x0 τ)⁻¹ *ᵥ u)).1`. Establish `b2` using `(frame_bound hr X h0 h2 hlt2 τ ((mat z1 τ)⁻¹ *ᵥ u)).2`. Establish `e : mat (lact γ z1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z1 τ` using `rfl`. Rewrite `b1` using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ hu]`.

Rewrite `b2` using `[e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1, ← Matrix.mulVec_mulVec]`. Establish `hn : 0 ≤ ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u)` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hE : ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2` using `pow_le_pow_left₀ hk (ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_le hr) 2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem opNormLe_of_ball (hr : 0 < r) (X : Data E r) {x0 z1 : Frame X.Ψ r} {γ : GL (Fin r) E}
    (h0 : IsOrth X x0) (h1 : IsOrth X z1) (h2 : IsOrth X (lact γ z1))
    (hlt : rhX X x0 z1 < 1 / (49 * (r : ℝ) ^ 2))
    (hlt2 : rhX X x0 (lact γ z1) < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x0 τ (γ : Matrix (Fin r) (Fin r) E) (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro u
  rw [ModeHalfA.maj_orth X h0, ModeHalfA.maj_orth X h0]
  change ReciprocityTheory.MultiplicativeHeights.normSq _ ≤ _ * ReciprocityTheory.MultiplicativeHeights.normSq _
  have hk := ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have hu1 : IsUnit (mat z1 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X z1 h1 τ)
  have b1 := (frame_bound hr X h0 h1 hlt τ ((mat x0 τ)⁻¹ *ᵥ u)).1
  have b2 := (frame_bound hr X h0 h2 hlt2 τ ((mat z1 τ)⁻¹ *ᵥ u)).2
  have e : mat (lact γ z1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z1 τ := rfl
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu] at b1
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1,
    ← Matrix.mulVec_mulVec] at b2
  have hn : 0 ≤ ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hk (ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_le hr) 2
  calc _ ≤ _ := b2
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 hk
    _ = ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 * ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hE hn

/- English proof (translation)
Introduce `E _ _ _ r X G g hsp hg hΓ hL' hΛ hU x hx hNC`. Take `⟨x1, h1, b, hb, rfl⟩` from `ortho_holds r X.toData x hx`. Establish `hx1 : x1 ∈ X.dom` using `IW.orth_mem_dom X.toData x1 h1`. Establish `hNC1` using `noContraction_of_rmul X hx1 hb hNC`. Use `⟨x1, h1, ⟨b, hb, rfl⟩, hΓ, hΛ, fun γ hγ hne z hz hlt => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt2`. Rewrite `hlt2` using `[not_le]`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Use `rhX_nonneg h1 hz` as an intermediate fact.

Simplify using `at hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z1, hz1, b', hb', rfl⟩` from `ortho_holds r X.toData z hz`. Rewrite `hlt2` using `[FundSetPf.lact_rmul, rhX_rmul _ _ hb']`. Rewrite `hlt` using `[rhX_rmul _ _ hb']`.

Establish `h2` using `isOrth_lact_of_isUStab (hΛ γ hγ) hz1`. Conclude with `hne (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hsp hg G hL' hU x1 hx1 hNC1 γ hγ (opNormLe_of_ball hr X.toData h1 hz1 h2 hlt hlt2))`.
-/
theorem freeBall_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  intro E _ _ _ r X G g hsp hg hΓ hL' hΛ hU x hx hNC
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 : x1 ∈ X.dom := IW.orth_mem_dom X.toData x1 h1
  have hNC1 := noContraction_of_rmul X hx1 hb hNC
  refine ⟨x1, h1, ⟨b, hb, rfl⟩, hΓ, hΛ, fun γ hγ hne z hz hlt => ?_⟩
  by_contra hlt2
  rw [not_le] at hlt2
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have := rhX_nonneg h1 hz
    simp at hlt
    linarith
  obtain ⟨z1, hz1, b', hb', rfl⟩ := ortho_holds r X.toData z hz
  rw [FundSetPf.lact_rmul, rhX_rmul _ _ hb'] at hlt2
  rw [rhX_rmul _ _ hb'] at hlt
  have h2 := isOrth_lact_of_isUStab (hΛ γ hγ) hz1
  exact hne (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hsp hg G hL' hU x1 hx1 hNC1 γ hγ
    (opNormLe_of_ball hr X.toData h1 hz1 h2 hlt hlt2))

end GlobalTheory.FreeBallAt
