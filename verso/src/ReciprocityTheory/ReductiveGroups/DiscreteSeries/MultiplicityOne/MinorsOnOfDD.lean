import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntIntegrableOf

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Set `L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ` to `(innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)`. Establish `hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ` using `fun A => by`. Simplify using `[L, innerSL_apply_apply]`. Establish `hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ` using `fun c A => by`. Rewrite using `[map_smul, hL, smul_eq_mul]`.

Use `⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]`. Use `congr 1`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)`.
-/
theorem repro_scalar (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) {u v : X.Hs} (e f : Wp)
    (hI : Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG)
    (hR : beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ) D.μG ∧
    ⟪e, beOp D X u v f⟫_ℂ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ ∂D.μG := by
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)
  have hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ := fun A => by
    simp [L, innerSL_apply_apply]
  have hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ := fun c A => by
    rw [map_smul, hL, smul_eq_mul]
  refine ⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩
  rw [hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)

/- English proof (translation)
Take `⟨Cc, hCc0, hCc⟩` from `coef_bound X ha0 hu`. Take `⟨Cb, hCb⟩` from `hbv`. Establish `hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v) D.μG` using `(show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)`. Use `((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_` and prove the remaining obligations. Use `filter_upwards [ae_G D] with y hy`.

Rewrite using `[norm_smul]`. Establish `e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b`. Rewrite using `[← Real.rpow_add (gN_pos hy)]`. Put the polynomial expressions in normal form. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem opint (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {b : ℝ}
    (hab : AB k r ≤ X.a - b) {u v : X.Hs} (hu : u ∈ Vfl X)
    (hbv : ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨Cc, hCc0, hCc⟩ := coef_bound X ha0 hu
  obtain ⟨Cb, hCb⟩ := hbv
  have hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG :=
    (show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from
      (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)
  refine ((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_
  filter_upwards [ae_G D] with y hy
  rw [norm_smul]
  have e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b := by
    rw [← Real.rpow_add (gN_pos hy)]; ring_nf
  rw [e]
  calc ‖⟪X.σ (Matrix.of y) X.w, u⟫_ℂ‖ * ‖beOp D X (X.σ (Matrix.of y) X.w) v‖
      ≤ (Cc * gN (Matrix.of y) ^ (-X.a)) * (Cb * gN (Matrix.of y) ^ b) :=
        mul_le_mul (hCc _ hy) (hCb _ hy) (norm_nonneg _)
          (mul_nonneg hCc0 (Real.rpow_nonneg (gN_nonneg _) _))
    _ = _ := by ring

/- English proof (translation)
Use `vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h` and prove the remaining obligations. Set `L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ` to `(innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)`. Set `L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ` to `(innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)`. Establish `m2` using `L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)`. Establish `m4` using `L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)`.

Conclude with `(m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)`. Take `⟨C₂, h₂⟩` from `hbe u₂ hu₂`. Take `⟨C₄, h₄⟩` from `hbe u₄ hu₄`. Use `⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ + ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Mn]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← norm_mul, ← norm_mul]`. Conclude with `norm_sub_le _ _`. Use `_ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ + (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := add_le_add (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _)) (mul_le_mul_of …`. Use `_ = _ := by ring`.

Introduce `u hu`. Take `⟨i2, r2⟩` from `repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)`. Take `⟨i4, r4⟩` from `repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)`. Establish `e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ - (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X …` using `fun y => by simp only [Mn]; ring`. Use `show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG`.

Simplify using `only [e5]`. Rewrite using `[integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]`. Simplify using `only [Mn]`. Rewrite using `[r2, r4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ext1 (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {d b : ℝ}
    (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    {u₂ u₄ : X.Hs} (hu₂ : u₂ ∈ Vfl X) (hu₄ : u₄ ∈ Vfl X) (u₃ : X.Hs) (e₁ e₂ e₃ e₄ : Wp)
    (h : ∀ φ : Mat k r → ℂ, IsTestG φ → Mn D X (sigInt D X φ X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) :
    ∀ u ∈ Vfl X, Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  refine vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h
  · let L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)
    let L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)
    have m2 := L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)
    have m4 := L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)
    exact (m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)
  · obtain ⟨C₂, h₂⟩ := hbe u₂ hu₂
    obtain ⟨C₄, h₄⟩ := hbe u₄ hu₄
    refine ⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
      ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩
    simp only [Mn]
    calc ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
          ⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖
        ≤ ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          ‖⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₄ y hy) (by positivity))) (norm_nonneg _))
      _ = _ := by ring
  · intro u hu
    obtain ⟨i2, r2⟩ := repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)
    obtain ⟨i4, r4⟩ := repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)
    have e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ =
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₄ e₄⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ := fun y => by simp only [Mn]; ring
    show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG
    simp only [e5]
    rw [integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]
    simp only [Mn]
    rw [r2, r4]
    ring

/- English proof (translation)
Unfold `Mn`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mn_swap (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₃ u₂ u₁ u₄ e₃ e₂ e₁ e₄ = -Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ := by
  unfold Mn; ring

/- English proof (translation)
Establish `kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp, ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ`. Introduce `u hu v hv e f`. Rewrite using `[hH v hv u hu e f, inner_conj_symm]`. Unfold `Mn`. Rewrite using `[kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]`.

Simplify using `only [map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mn_herm (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    {u₁ u₂ u₃ u₄ : X.Hs} (h₁ : u₁ ∈ Vfl X) (h₂ : u₂ ∈ Vfl X) (h₃ : u₃ ∈ Vfl X) (h₄ : u₄ ∈ Vfl X)
    (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₂ u₁ u₄ u₃ e₂ e₁ e₄ e₃ = starRingEnd ℂ (Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄) := by
  have kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp,
      ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ := by
    intro u hu v hv e f
    rw [hH v hv u hu e f, inner_conj_symm]
  unfold Mn
  rw [kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]
  simp only [map_sub, map_mul]
  ring

/- English proof (translation)
Establish `hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X`. Introduce and unpack `u ⟨φ, hφ, rfl⟩`. Conclude with `dd_mem D X ha0 hφ`. Establish `hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X` using `fun φ hφ => ⟨φ, hφ, rfl⟩`. Establish `S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp, Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0`.

Introduce `u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄`. Conclude with `ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄ (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁`. Establish `S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp, Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0`. Introduce `u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄`. Rewrite using `[← neg_eq_zero, ← mn_swap]`.

Conclude with `ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄ (fun φ hφ => by`. Rewrite using `[← neg_eq_zero, ← mn_swap]`. Conclude with `S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃`. Establish `S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp, Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0`. Introduce `u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄`.

Rewrite using `[mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃, S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]`. Establish `S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp, Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0`. Introduce `u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄`. Conclude with `ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄ (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁`. Introduce `u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄`.

Establish `: Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0`. Rewrite using `[← neg_eq_zero, ← mn_swap]`. Conclude with `ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄ (fun φ hφ => by`. Rewrite using `[← neg_eq_zero, ← mn_swap]`. Conclude with `S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃`.

Conclude with `sub_eq_zero.1 this`.
-/
theorem minorsOn_of_DD (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a)
    {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hDD : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) : MinorsOn D X := by
  have hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X := fun φ hφ => ⟨φ, hφ, rfl⟩
  have S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  have S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  have S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃,
      S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]
  have S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
  have : Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  exact sub_eq_zero.1 this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
