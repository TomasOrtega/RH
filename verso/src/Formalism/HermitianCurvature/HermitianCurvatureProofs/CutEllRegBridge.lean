import Formalism.UnipotentAdelicQuotients.EllReg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open MeasureTheory
open scoped ContDiff

def EllRegBridge : Prop := ZetaZeros.D.EllReg.Internal → EllRegW

section bridge

variable {d : ℕ}

noncomputable abbrev brT (d : ℕ) : ZetaZeros.D.EllReg.E d ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ

/- English proof (translation)
Unfold `ZetaZeros.D.EllReg.ev`. Both sides reduce to the same expression.
-/
lemma brT_ev (j : Fin d) : brT d (ZetaZeros.D.EllReg.ev j) = Pi.single j 1 := by
  unfold ZetaZeros.D.EllReg.ev
  rfl

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons j w ih`. Use function extensionality and compare the values at `x`. Use `show fderiv ℝ (ZetaZeros.D.EllReg.dw w (f ∘ brT d)) x (ZetaZeros.D.EllReg.ev j) = fderiv ℝ (pdc w f) (brT d x) (Pi.single j 1)`.

Rewrite using `[ih, (brT d).comp_right_fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, brT_ev]`.
-/
lemma dw_comp_brT (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    ZetaZeros.D.EllReg.dw w (f ∘ brT d) = pdc w f ∘ brT d := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (ZetaZeros.D.EllReg.dw w (f ∘ brT d)) x (ZetaZeros.D.EllReg.ev j) =
      fderiv ℝ (pdc w f) (brT d x) (Pi.single j 1)
    rw [ih, (brT d).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, brT_ev]

noncomputable def brSys {ι : Type} (P : ι → SOp d) : ZetaZeros.D.EllReg.Sys d ι where
  ord i := (P i).ord
  a i n w := if h : n < (P i).ord + 1 then (P i).a ⟨n, h⟩ w ∘ brT d else 0

/- English proof (translation)
Unfold `ZetaZeros.D.EllReg.Sys.tr ZetaZeros.D.EllReg.trOp SOp.tr`. Rewrite using `[Finset.sum_range]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `e : (fun y => (brSys P).a i k w y * (φ ∘ brT d) y) = (fun y' => (P i).a k w y' * φ y') ∘ brT d`.

Use function extensionality and compare the values at `y`. Simplify using `only [brSys, Function.comp_apply]`. Rewrite using `[dif_pos (show (k : ℕ) < (P i).ord + 1 from k.isLt)]`. Both sides reduce to the same expression. Rewrite using `[e, dw_comp_brT]`.

Both sides reduce to the same expression.
-/
lemma brSys_tr {ι : Type} (P : ι → SOp d) (i : ι) (φ : (Fin d → ℝ) → ℂ) (x : ZetaZeros.D.EllReg.E d) :
    (brSys P).tr i (φ ∘ brT d) x = (P i).tr φ (brT d x) := by
  unfold ZetaZeros.D.EllReg.Sys.tr ZetaZeros.D.EllReg.trOp SOp.tr
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have e : (fun y => (brSys P).a i k w y * (φ ∘ brT d) y) =
      (fun y' => (P i).a k w y' * φ y') ∘ brT d := by
    funext y
    simp only [brSys, Function.comp_apply]
    rw [dif_pos (show (k : ℕ) < (P i).ord + 1 from k.isLt)]
    rfl
  rw [e, dw_comp_brT]
  rfl

/- English proof (translation)
Unfold `ZetaZeros.D.EllReg.Sys.symb SOp.symb`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [brSys, dif_pos (Nat.lt_succ_self _)]`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
lemma brSys_symb {ι : Type} (P : ι → SOp d) (i : ι) (x ξ : ZetaZeros.D.EllReg.E d) :
    (brSys P).symb i x ξ = (P i).symb (brT d x) (brT d ξ) := by
  unfold ZetaZeros.D.EllReg.Sys.symb SOp.symb
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [brSys, dif_pos (Nat.lt_succ_self _)]
  rw [mul_comm]
  rfl

end bridge

/- English proof (translation)
Introduce `hI d ι _ P U u hU ha hu hweak hsymb`. Establish `hHyp : ZetaZeros.D.EllReg.Hyp (brSys P) (brT d ⁻¹' U) (u ∘ brT d)`. Use `⟨hU.preimage (brT d).continuous, ?_, ?_, hu.comp (brT d).continuous.continuousOn (fun x hx => hx), ?_⟩` and prove the remaining obligations. Introduce `i n w`. Simplify using `only [brSys]`.

Use `split_ifs with h`. Conclude with `(ha i ⟨n, h⟩ w).comp_continuousLinearMap ((brT d : ZetaZeros.D.EllReg.E d →L[ℝ] (Fin d → ℝ)))`. Conclude with `contDiffOn_const`. Introduce `x hx ξ hξ`. Establish `hξ' : brT d ξ ≠ 0` using `fun h => hξ ((brT d).injective (h.trans (map_zero (brT d)).symm))`.

Take `⟨i, hi⟩` from `hsymb (brT d x) hx (brT d ξ) hξ'`. Conclude with `⟨i, by rw [brSys_symb]; exact hi⟩`. Introduce `i φ hφ hφc hφU`. Establish `hψ : ContDiff ℝ ∞ (φ ∘ (brT d).symm)` using `hφ.comp (brT d).symm.contDiff`. Establish `hψc : HasCompactSupport (φ ∘ (brT d).symm)` using `hφc.comp_homeomorph (brT d).symm.toHomeomorph`.

Establish `hψU : tsupport (φ ∘ (brT d).symm) ⊆ U`. Introduce `y hy`. Establish `hy' : y ∈ tsupport (φ ∘ (brT d).symm.toHomeomorph)` using `hy`. Rewrite `hy'` using `[tsupport_comp_eq_preimage φ (brT d).symm.toHomeomorph]`. Establish `h1` using `hφU hy'`.

Establish `h2 : brT d ((brT d).symm y) ∈ U` using `h1`. Rewrite `h2` using `[ContinuousLinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hφeq : φ = (φ ∘ (brT d).symm) ∘ brT d`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Establish `h1` using `hweak i (φ ∘ (brT d).symm) hψ hψc hψU`. Rewrite using `[hφeq]`. Repeatedly rewrite using `[brSys_tr]`. Rewrite using `[← h1]`. Conclude with `(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding (fun y => u y * (P i).tr (φ ∘ (brT d).symm) y)`.

Establish `key` using `hI d ι (brSys P) (brT d ⁻¹' U) (u ∘ brT d) hHyp`. Establish `h2` using `key.comp_continuousLinearMap (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d))`. Establish `e1 : (u ∘ brT d) ∘ (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) = u`. Use function extensionality and compare the values at `x`. Use `show u (brT d ((brT d).symm x)) = u x`.

Rewrite using `[ContinuousLinearEquiv.apply_symm_apply]`. Establish `e2 : (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) ⁻¹' (brT d ⁻¹' U) = U`. Use extensionality with `x`. Use `show brT d ((brT d).symm x) ∈ U ↔ x ∈ U`. Rewrite using `[ContinuousLinearEquiv.apply_symm_apply]`.

Rewrite `h2` using `[e1, e2]`. Conclude with `h2`.
-/
theorem elliptic_regularity_transfer_holds : EllRegBridge := by
  intro hI d ι _ P U u hU ha hu hweak hsymb
  have hHyp : ZetaZeros.D.EllReg.Hyp (brSys P) (brT d ⁻¹' U) (u ∘ brT d) := by
    refine ⟨hU.preimage (brT d).continuous, ?_, ?_, hu.comp (brT d).continuous.continuousOn (fun x hx => hx), ?_⟩
    · intro i n w
      simp only [brSys]
      split_ifs with h
      · exact (ha i ⟨n, h⟩ w).comp_continuousLinearMap ((brT d : ZetaZeros.D.EllReg.E d →L[ℝ] (Fin d → ℝ)))
      · exact contDiffOn_const
    · intro x hx ξ hξ
      have hξ' : brT d ξ ≠ 0 := fun h => hξ ((brT d).injective (h.trans (map_zero (brT d)).symm))
      obtain ⟨i, hi⟩ := hsymb (brT d x) hx (brT d ξ) hξ'
      exact ⟨i, by rw [brSys_symb]; exact hi⟩
    · intro i φ hφ hφc hφU
      have hψ : ContDiff ℝ ∞ (φ ∘ (brT d).symm) := hφ.comp (brT d).symm.contDiff
      have hψc : HasCompactSupport (φ ∘ (brT d).symm) := hφc.comp_homeomorph (brT d).symm.toHomeomorph
      have hψU : tsupport (φ ∘ (brT d).symm) ⊆ U := by
        intro y hy
        have hy' : y ∈ tsupport (φ ∘ (brT d).symm.toHomeomorph) := hy
        rw [tsupport_comp_eq_preimage φ (brT d).symm.toHomeomorph] at hy'
        have h1 := hφU hy'
        have h2 : brT d ((brT d).symm y) ∈ U := h1
        rwa [ContinuousLinearEquiv.apply_symm_apply] at h2
      have hφeq : φ = (φ ∘ (brT d).symm) ∘ brT d := by
        funext x
        simp
      have h1 := hweak i (φ ∘ (brT d).symm) hψ hψc hψU
      rw [hφeq]
      simp_rw [brSys_tr]
      rw [← h1]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
        (fun y => u y * (P i).tr (φ ∘ (brT d).symm) y)
  have key := hI d ι (brSys P) (brT d ⁻¹' U) (u ∘ brT d) hHyp
  have h2 := key.comp_continuousLinearMap (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d))
  have e1 : (u ∘ brT d) ∘ (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) = u := by
    funext x
    show u (brT d ((brT d).symm x)) = u x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have e2 : (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) ⁻¹' (brT d ⁻¹' U) = U := by
    ext x
    show brT d ((brT d).symm x) ∈ U ↔ x ∈ U
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [e1, e2] at h2
  exact h2

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
