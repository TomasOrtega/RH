import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology

namespace MCInvEntryDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}

/- English proof (translation)
Simplify using `only [det_apply, Units.smul_def, zsmul_eq_mul]`. Conclude with `DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i q => M q (σ i) i) fun i _ => (hM _ _).hasFDerivAt).differentiableAt`.
-/
theorem differentiableAt_det {M : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hM : ∀ j l, DifferentiableAt ℝ (fun q => M q j l) p) :
    DifferentiableAt ℝ (fun q => (M q).det) p := by
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul
      (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i q => M q (σ i) i)
        fun i _ => (hM _ _).hasFDerivAt).differentiableAt

/- English proof (translation)
Rewrite using `[inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]`.
-/
theorem inv_entry_eq (A : Matrix (Fin g) (Fin g) ℝ) (j l : Fin g) :
    A⁻¹ j l = (A.det)⁻¹ * (A.updateRow l (Pi.single j 1)).det := by
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]

/- English proof (translation)
Simplify using `only [inv_entry_eq]`. Use `((differentiableAt_det hY).inv hdet).mul (differentiableAt_det fun k m => ?_)` and prove the remaining obligations. Simplify using `only [updateRow_apply]`. Use `split_ifs`. Conclude with `differentiableAt_const _`.

Conclude with `hY k m`.
-/
theorem differentiableAt_inv_entry {Y : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hY : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p) (hdet : (Y p).det ≠ 0) (j l : Fin g) :
    DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p := by
  simp only [inv_entry_eq]
  refine ((differentiableAt_det hY).inv hdet).mul (differentiableAt_det fun k m => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hY k m

end MCInvEntryDeriv

/- English proof (translation)
Introduce `E _ _ g Y p c b hc hpsd hY`. Establish `hpd : (Y p).PosDef` using `MCBounds.posDef_of_ge hc hpsd`. Establish `hdet : (Y p).det ≠ 0` using `hpd.det_pos.ne'`. Establish `hYd : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p` using `fun j l => (hY j l).1`. Apply the tactic sequence `have hZd := MCInvEntryDeriv.differentiableAt_inv_entry hYd hdet`.

Establish `hnear : ∀ᶠ q in 𝓝 p, (Y q).det ≠ 0` using `(MCInvEntryDeriv.differentiableAt_det hYd).continuousAt.eventually_ne hdet`. Establish `key : ∀ j m, ∑ s, Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p = -∑ s, (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p`. Introduce `j m`. Establish `hconst : (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) =ᶠ[𝓝 p] fun _ => (1 : Matrix (Fin g) (Fin g) ℝ) j m` using `by filter_upwards [hnear] with q hq`. Rewrite using `[← mul_apply, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq)]`.

Establish `h1 : fderiv ℝ (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) p = ∑ s, (Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p + (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p)`. Rewrite using `[fderiv_fun_sum (u := Finset.univ) (A := fun s q => Y q j s * (Y q)⁻¹ s m) (fun s _ => (hYd j s).mul (hZd s m))]`. Conclude with `Finset.sum_congr rfl fun s _ => fderiv_fun_mul (hYd j s) (hZd s m)`. Rewrite `h1` using `[hconst.fderiv_eq, fderiv_const_apply, Finset.sum_add_distrib]`. Conclude with `eq_neg_of_add_eq_zero_left h1.symm`.

Establish `form : ∀ j l, fderiv ℝ (fun q => (Y q)⁻¹ j l) p = -∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p`. Introduce `j l`. Establish `hZY : (Y p)⁻¹ * Y p = 1` using `nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hZY]`.

Simplify using `[one_apply]`. Use `_ = ∑ m, (Y p)⁻¹ j m • ∑ s, Y p m s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by`. Simplify using `only [mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = _ := by`.

Simplify using `only [key, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib]`. Introduce `j l`. Use `⟨hZd j l, ?_⟩` and prove the remaining obligations. Rewrite using `[form, norm_neg]`. Establish `hinv` using `h₁ g (Y p) c hc hpsd`.

Establish `hci : 0 ≤ c⁻¹` using `inv_nonneg.mpr hc.le`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_mul]`. Conclude with `mul_le_mul (mul_le_mul (hinv j m) (hinv s l) (abs_nonneg _) hci) (hY m s).2 (norm_nonneg _) (mul_nonneg hci hci)`.

Use `_ = (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem InvEntryDeriv.proof (h₁ : InvEntryBound.Statement) : InvEntryDeriv.Statement := by
  intro E _ _ g Y p c b hc hpsd hY
  have hpd : (Y p).PosDef := MCBounds.posDef_of_ge hc hpsd
  have hdet : (Y p).det ≠ 0 := hpd.det_pos.ne'
  have hYd : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p := fun j l => (hY j l).1
  have hZd := MCInvEntryDeriv.differentiableAt_inv_entry hYd hdet
  have hnear : ∀ᶠ q in 𝓝 p, (Y q).det ≠ 0 :=
    (MCInvEntryDeriv.differentiableAt_det hYd).continuousAt.eventually_ne hdet

  have key : ∀ j m, ∑ s, Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p =
      -∑ s, (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p := by
    intro j m
    have hconst : (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) =ᶠ[𝓝 p]
        fun _ => (1 : Matrix (Fin g) (Fin g) ℝ) j m := by
      filter_upwards [hnear] with q hq
      rw [← mul_apply, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq)]
    have h1 : fderiv ℝ (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) p =
        ∑ s, (Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p +
          (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p) := by
      rw [fderiv_fun_sum (u := Finset.univ) (A := fun s q => Y q j s * (Y q)⁻¹ s m)
        (fun s _ => (hYd j s).mul (hZd s m))]
      exact Finset.sum_congr rfl fun s _ => fderiv_fun_mul (hYd j s) (hZd s m)
    rw [hconst.fderiv_eq, fderiv_const_apply, Finset.sum_add_distrib] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have form : ∀ j l, fderiv ℝ (fun q => (Y q)⁻¹ j l) p =
      -∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p := by
    intro j l
    have hZY : (Y p)⁻¹ * Y p = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    calc fderiv ℝ (fun q => (Y q)⁻¹ j l) p
        = ∑ s, ((Y p)⁻¹ * Y p) j s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          rw [hZY]; simp [one_apply]
      _ = ∑ m, (Y p)⁻¹ j m • ∑ s, Y p m s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          simp only [mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          simp only [key, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib]
  intro j l
  refine ⟨hZd j l, ?_⟩
  rw [form, norm_neg]
  have hinv := h₁ g (Y p) c hc hpsd
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  calc ‖∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖
      ≤ ∑ m, ∑ s, ‖((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
    _ ≤ ∑ _m : Fin g, ∑ _s : Fin g, c⁻¹ * c⁻¹ * b := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun s _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (mul_le_mul (hinv j m) (hinv s l) (abs_nonneg _) hci) (hY m s).2
          (norm_nonneg _) (mul_nonneg hci hci)
    _ = (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end GroundTheory.Heights₂.Heights
