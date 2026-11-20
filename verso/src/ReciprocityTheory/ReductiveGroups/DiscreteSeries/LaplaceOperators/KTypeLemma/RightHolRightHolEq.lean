import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `h : (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) = fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i`. Use function extensionality and compare the values at `z`. Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`. Rewrite using `[h]`. Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)`.
-/
private theorem contDiff_det_k_type {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) =
      fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i := by
    funext z
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.adjugate_apply]`. Establish `hrow : ContDiff ℂ k (fun x : Matrix (Fin m) (Fin m) ℂ => x.updateRow j (Pi.single i 1))`. Use `contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hab : a = j`.

Substitute `hab` using the available equality. Simplify using `only [Matrix.updateRow_self]`. Conclude with `contDiff_const`. Simplify using `only [Matrix.updateRow_ne hab]`. Conclude with `contDiff_pi.1 (contDiff_pi.1 contDiff_id a) b`.

Conclude with `contDiff_det_k_type.comp hrow`.
-/
private theorem contDiff_adjugate' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.adjugate_apply]
  have hrow : ContDiff ℂ k
      (fun x : Matrix (Fin m) (Fin m) ℂ => x.updateRow j (Pi.single i 1)) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    by_cases hab : a = j
    · subst hab
      simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne hab]
      exact contDiff_pi.1 (contDiff_pi.1 contDiff_id a) b
  exact contDiff_det_k_type.comp hrow

/- English proof (translation)
Establish `h : (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) = fun z => (z.det)⁻¹ • z.adjugate`. Use function extensionality and compare the values at `z`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[h]`. Conclude with `(contDiff_det_k_type.contDiffOn.inv fun z hz => hz).smul contDiff_adjugate'.contDiffOn`.
-/
private theorem contDiffOn_inv_det_ne_zero' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiffOn ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) {z | z.det ≠ 0} := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) = fun z => (z.det)⁻¹ • z.adjugate := by
    funext z
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (contDiff_det_k_type.contDiffOn.inv fun z hz => hz).smul contDiff_adjugate'.contDiffOn

/- English proof (translation)
Distinguish the cases in `h : i ≤ n`. Simplify using `only [lead, dif_pos h]`. Establish `hs : ContDiff ℂ k (fun z : Matrix (Fin n) (Fin n) ℂ => z.submatrix (Fin.castLE h) (Fin.castLE h))` using `contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_pi.1 (contDiff_pi.1 contDiff_id (Fin.castLE h a)) (Fin.castLE h b)`. Conclude with `contDiff_det_k_type.comp hs`. Simplify using `only [lead, dif_neg h]`.

Conclude with `contDiff_const`.
-/
private theorem contDiff_lead_k_type {k : WithTop ℕ∞} (i : ℕ) :
    ContDiff ℂ k (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  by_cases h : i ≤ n
  · simp only [lead, dif_pos h]
    have hs : ContDiff ℂ k
        (fun z : Matrix (Fin n) (Fin n) ℂ => z.submatrix (Fin.castLE h) (Fin.castLE h)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b =>
        contDiff_pi.1 (contDiff_pi.1 contDiff_id (Fin.castLE h a)) (Fin.castLE h b)
    exact contDiff_det_k_type.comp hs
  · simp only [lead, dif_neg h]
    exact contDiff_const

/- English proof (translation)
Establish `h : OmegaSet n = ⋂ i : Fin n, {z : Matrix (Fin n) (Fin n) ℂ | lead ((i : ℕ) + 1) z ≠ 0}`. Use extensionality with `z`. Simplify using `[OmegaSet]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead_k_type (k := 0) _).continuous continuous_const`.
-/
private theorem isOpen_omegaSet' : IsOpen (OmegaSet n) := by
  have h : OmegaSet n = ⋂ i : Fin n, {z : Matrix (Fin n) (Fin n) ℂ | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead_k_type (k := 0) _).continuous continuous_const

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Introduce `h`. Establish `h0 : z⁻¹ = 0` using `Matrix.nonsing_inv_apply_not_isUnit z (by simpa [isUnit_iff_ne_zero] using h)`. Establish `hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0` using `hz`.

Establish `h1 : 1 ≤ n` using `hn`. Conclude with `hz' ⟨0, hn⟩ (by rw [h0]; simp [lead, h1])`.
-/
private theorem det_ne_zero_of_mem_omegaP {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) : z.det ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · intro h
    have h0 : z⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit z (by simpa [isUnit_iff_ne_zero] using h)
    have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0 := hz
    have h1 : 1 ≤ n := hn
    exact hz' ⟨0, hn⟩ (by rw [h0]; simp [lead, h1])

/- English proof (translation)
Establish `h : OmegaP n = {z : Matrix (Fin n) (Fin n) ℂ | z.det ≠ 0} ∩ (fun z => z⁻¹) ⁻¹' OmegaSet n`. Use extensionality with `z`. Conclude with `⟨fun hz => ⟨det_ne_zero_of_mem_omegaP hz, hz⟩, fun hz => hz.2⟩`. Rewrite using `[h]`. Conclude with `(contDiffOn_inv_det_ne_zero' (k := 0)).continuousOn.isOpen_inter_preimage (isOpen_ne_fun (contDiff_det_k_type (k := 0)).continuous continuous_const) isOpen_omegaSet'`.
-/
private theorem isOpen_omegaP : IsOpen (OmegaP n) := by
  have h : OmegaP n =
      {z : Matrix (Fin n) (Fin n) ℂ | z.det ≠ 0} ∩ (fun z => z⁻¹) ⁻¹' OmegaSet n := by
    ext z
    exact ⟨fun hz => ⟨det_ne_zero_of_mem_omegaP hz, hz⟩, fun hz => hz.2⟩
  rw [h]
  exact (contDiffOn_inv_det_ne_zero' (k := 0)).continuousOn.isOpen_inter_preimage
    (isOpen_ne_fun (contDiff_det_k_type (k := 0)).continuous continuous_const) isOpen_omegaSet'

/- English proof (translation)
The claim follows from `isOpen_omegaP.mem_nhds hx`.
-/
theorem positiveOmega_mem_nhds {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : OmegaP n ∈ nhds x := isOpen_omegaP.mem_nhds hx

/- English proof (translation)
The claim follows from `isOpen_omegaP`.
-/
theorem isOpen_positiveOmega : IsOpen (OmegaP n) := isOpen_omegaP

/- English proof (translation)
Use `show fderiv ℂ G z (z * X) = fderiv ℂ H z (z * X)`. Rewrite using `[(h.eventuallyEq_of_mem (positiveOmega_mem_nhds hz)).fderiv_eq]`.
-/
theorem rightHol_congr_on_omega {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaP n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) :
    Rhol X G z = Rhol X H z := by
  show fderiv ℂ G z (z * X) = fderiv ℂ H z (z * X)
  rw [(h.eventuallyEq_of_mem (positiveOmega_mem_nhds hz)).fderiv_eq]

def matrixMulRightCLM (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem k2mMulRight_apply (Y w : Matrix (Fin n) (Fin n) ℂ) : matrixMulRightCLM Y w = w * Y := rfl

/- English proof (translation)
The claim follows from `(hF.contDiffAt (isOpen_omegaP.mem_nhds hz)).differentiableAt (by simp)`.
-/
theorem differentiableAt_of_contDiffOn_omega {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaP n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) :
    DifferentiableAt ℂ F z := (hF.contDiffAt (isOpen_omegaP.mem_nhds hz)).differentiableAt
    (by simp)

/- English proof (translation)
Establish `hd : DifferentiableAt ℂ (fderiv ℂ F) z` using `(hF.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero`. Establish `he : Rhol Y F = fun w => fderiv ℂ F w (matrixMulRightCLM Y w)` using `rfl`. Use `show fderiv ℂ (Rhol Y F) z (z * X) = _`. Establish `h3` using `hd.hasFDerivAt.clm_apply (matrixMulRightCLM Y).hasFDerivAt`. Rewrite using `[he]`.

Use `(congrArg (fun L => L (z * X)) h3.fderiv).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fderiv ℂ F z (matrixMulRightCLM Y (z * X)) + fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = _`. Rewrite using `[k2mMulRight_apply]`.
-/
theorem rightHol_rightHol_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Rhol X (Rhol Y F) z = fderiv ℂ F z (z * X * Y) + fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) := by
  have hd : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero
  have he : Rhol Y F = fun w => fderiv ℂ F w (matrixMulRightCLM Y w) := rfl
  show fderiv ℂ (Rhol Y F) z (z * X) = _
  have h3 := hd.hasFDerivAt.clm_apply (matrixMulRightCLM Y).hasFDerivAt
  rw [he]
  refine (congrArg (fun L => L (z * X)) h3.fderiv).trans ?_
  change fderiv ℂ F z (matrixMulRightCLM Y (z * X)) + fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = _
  rw [k2mMulRight_apply]

/- English proof (translation)
Apply the tactic sequence `have hs : IsSymmSndFDerivAt ℂ F z := hF.isSymmSndFDerivAt (by first | simp [minSmoothness_of_isRCLikeNormedField] | simp | exact le_rfl)`. Establish `h2 : fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = fderiv ℂ (fderiv ℂ F) z (z * Y) (z * X)` using `hs _ _`. Rewrite using `[rightHol_rightHol_eq hF, rightHol_rightHol_eq hF, h2]`. Simplify using `only [Rhol]`. Rewrite using `[mul_sub, ← mul_assoc, ← mul_assoc, map_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rightHol_commutator {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Rhol X (Rhol Y F) z - Rhol Y (Rhol X F) z = Rhol (X * Y - Y * X) F z := by
  have hs : IsSymmSndFDerivAt ℂ F z := hF.isSymmSndFDerivAt
    (by first | simp [minSmoothness_of_isRCLikeNormedField] | simp | exact le_rfl)
  have h2 : fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = fderiv ℂ (fderiv ℂ F) z (z * Y) (z * X) :=
    hs _ _
  rw [rightHol_rightHol_eq hF, rightHol_rightHol_eq hF, h2]
  simp only [Rhol]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
  ring

/- English proof (translation)
Simplify using `only [Rhol, mul_sub, map_sub]`.
-/
theorem rightHol_sub (X Y : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (z : Matrix (Fin n) (Fin n) ℂ) : Rhol (X - Y) F z = Rhol X F z - Rhol Y F z := by
  simp only [Rhol, mul_sub, map_sub]

/- English proof (translation)
Conclude with `contDiffOn_inv_det_ne_zero'`.
-/
theorem contDiffOn_inv_det_ne_zero :
    ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) {z | z.det ≠ 0} := by
  exact contDiffOn_inv_det_ne_zero'

/- English proof (translation)
Establish `hinv : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) (OmegaP n)` using `contDiffOn_inv_det_ne_zero'.mono fun z hz => det_ne_zero_of_mem_omegaP hz`. Use `show ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => ∏ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ^ (-(μ i - muNext μ i))) (OmegaP n)`. Use `contDiffOn_prod fun i _ => ?_` and prove the remaining obligations. Establish `hg : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z⁻¹) (OmegaP n)` using `(contDiff_lead_k_type _).comp_contDiffOn hinv`. Establish `hne : ∀ z ∈ OmegaP n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0` using `fun z hz => (show ∀ j : Fin n, lead ((j : ℕ) + 1) z⁻¹ ≠ 0 from hz) i`.

Break down `Int.eq_nat_or_neg (-(μ i - muNext μ i)) with ⟨k, hk | hk⟩` into its components or cases. Simplify using `only [hk, zpow_natCast]`. Conclude with `hg.pow k`. Simplify using `only [hk, _root_.zpow_neg, zpow_natCast]`. Conclude with `(hg.pow k).inv fun z hz => pow_ne_zero _ (hne z hz)`.
-/
theorem contDiffOn_powerDet (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiP μ) (OmegaP n) := by
  have hinv : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) (OmegaP n) :=
    contDiffOn_inv_det_ne_zero'.mono fun z hz => det_ne_zero_of_mem_omegaP hz
  show ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
    ∏ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ^ (-(μ i - muNext μ i))) (OmegaP n)
  refine contDiffOn_prod fun i _ => ?_
  have hg : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z⁻¹) (OmegaP n) :=
    (contDiff_lead_k_type _).comp_contDiffOn hinv
  have hne : ∀ z ∈ OmegaP n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0 := fun z hz =>
    (show ∀ j : Fin n, lead ((j : ℕ) + 1) z⁻¹ ≠ 0 from hz) i
  rcases Int.eq_nat_or_neg (-(μ i - muNext μ i)) with ⟨k, hk | hk⟩
  · simp only [hk, zpow_natCast]
    exact hg.pow k
  · simp only [hk, _root_.zpow_neg, zpow_natCast]
    exact (hg.pow k).inv fun z hz => pow_ne_zero _ (hne z hz)

/- English proof (translation)
Simplify using `only [Lhol, neg_mul, map_neg]`.
-/
theorem leftHol_neg (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol (-X) F z = -Lhol X F z := by
  simp only [Lhol, neg_mul, map_neg]

/- English proof (translation)
Establish `h` using `tb_hWord_phiP μ [X] z hz`. Rewrite using `[← leftHol_neg]`. Conclude with `h`.
-/
theorem rightHol_powerDet_eq_neg_leftHol (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaP n) : Rhol X (PhiP μ) z = -Lhol X (PhiM μ) z⁻¹ := by
  have h := tb_hWord_phiP μ [X] z hz
  rw [← leftHol_neg]
  exact h

/- English proof (translation)
Rewrite using `[rightHol_powerDet_eq_neg_leftHol μ _ hz, lhol_phiM_lower μ hab hz, neg_zero]`.
-/
theorem rightHol_powerDet_lower_eq_zero (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaP n) : Rhol (Matrix.single a b 1) (PhiP μ) z = 0 := by
  rw [rightHol_powerDet_eq_neg_leftHol μ _ hz, lhol_phiM_lower μ hab hz, neg_zero]

/- English proof (translation)
Rewrite using `[rightHol_powerDet_eq_neg_leftHol μ _ hz, lhol_phiM_diag μ a hz]`. Simplify using `only [PhiP, neg_mul, neg_neg]`.
-/
theorem rightHol_powerDet_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaP n) : Rhol (Matrix.single a a 1) (PhiP μ) z = (μ a : ℂ) * PhiP μ z := by
  rw [rightHol_powerDet_eq_neg_leftHol μ _ hz, lhol_phiM_diag μ a hz]
  simp only [PhiP, neg_mul, neg_neg]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
