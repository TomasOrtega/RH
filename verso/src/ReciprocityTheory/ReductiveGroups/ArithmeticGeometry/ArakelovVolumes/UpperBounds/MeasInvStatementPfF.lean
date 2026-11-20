import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def jac (w : Ix ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1

/- English proof (translation)
Establish `hsl : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => sl w w0 a b`. Introduce `w0 a b`. Apply the tactic sequence `by_cases h : b < a <;> simp [sl, h] <;> fun_prop`. Establish `hup : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => up w w0 a b`. Introduce `w0 a b`.

Apply the tactic sequence `by_cases h : b < a <;> simp [up, h] <;> fun_prop`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [lu, Matrix.mul_apply, Matrix.add_apply]`. Conclude with `continuous_finset_sum _ fun k _ => (continuous_const.add (hsl _ _ _)).mul (hup _ _ _)`.
-/
lemma continuous_lu : Continuous (lu (ι := ι) (r := r)) := by
  have hsl : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => sl w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [sl, h] <;> fun_prop
  have hup : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => up w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [up, h] <;> fun_prop
  refine continuous_pi fun i => ?_
  simp only [lu, Matrix.mul_apply, Matrix.add_apply]
  exact continuous_finset_sum _ fun k _ => (continuous_const.add (hsl _ _ _)).mul (hup _ _ _)

/- English proof (translation)
Unfold `jac`. Use `continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i.2.2 < i.2.1 <;> simp [h] <;> fun_prop`.
-/
lemma continuous_jac : Continuous (jac (ι := ι) (r := r)) := by
  unfold jac
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h] <;> fun_prop

/- English proof (translation)
Unfold `sS`. Establish `h : {w : Ix ι r → ℂ | ∀ (τ : ι) (b : Fin r), w (τ, b, b) ≠ 0} = ⋂ τ : ι, ⋂ b : Fin r, (fun w : Ix ι r → ℂ => w (τ, b, b)) ⁻¹' {0}ᶜ`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Conclude with `MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b => measurable_pi_apply _ (measurableSet_singleton 0).compl`.
-/
lemma measurableSet_sS : MeasurableSet (sS ι r) := by
  unfold sS
  have h : {w : Ix ι r → ℂ | ∀ (τ : ι) (b : Fin r), w (τ, b, b) ≠ 0} =
      ⋂ τ : ι, ⋂ b : Fin r, (fun w : Ix ι r → ℂ => w (τ, b, b)) ⁻¹' {0}ᶜ := by
    ext w
    simp
  rw [h]
  exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b =>
    measurable_pi_apply _ (measurableSet_singleton 0).compl

/- English proof (translation)
Establish `hae : ∀ᵐ v ∂(volume : Measure (Ix ι r → ℂ)), v ∈ lu '' sS ι r`. Use `measure_mono_null (fun v hv => ?_) (volume_BC_compl (ι := ι) (r := r))` and prove the remaining obligations. Conclude with `fun hB => hv (BC_subset_image (ι := ι) (r := r) hB)`. Rewrite using `[show ∫⁻ v, g v = ∫⁻ v in lu '' sS ι r, g v by rw [Measure.restrict_eq_self_of_ae_mem hae], lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_sS (fun w _ => (hasFDerivAt_lu w).hasFDerivWithinAt) lu_injOn g]`. Use `setLIntegral_congr_fun (measurableSet_sS (ι := ι) (r := r)) (fun w _ => ?_)` and prove the remaining obligations.

Rewrite using `[det_luD', abs_of_nonneg (Complex.normSq_nonneg _)]`. Both sides reduce to the same expression.
-/
theorem lintegral_lu (g : (Ix ι r → ℂ) → ENNReal) :
    ∫⁻ v, g v = ∫⁻ w in sS ι r, ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w) := by
  have hae : ∀ᵐ v ∂(volume : Measure (Ix ι r → ℂ)), v ∈ lu '' sS ι r := by
    refine measure_mono_null (fun v hv => ?_) (volume_BC_compl (ι := ι) (r := r))
    exact fun hB => hv (BC_subset_image (ι := ι) (r := r) hB)
  rw [show ∫⁻ v, g v = ∫⁻ v in lu '' sS ι r, g v by rw [Measure.restrict_eq_self_of_ae_mem hae],
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_sS
      (fun w _ => (hasFDerivAt_lu w).hasFDerivWithinAt) lu_injOn g]
  refine setLIntegral_congr_fun (measurableSet_sS (ι := ι) (r := r)) (fun w _ => ?_)
  rw [det_luD', abs_of_nonneg (Complex.normSq_nonneg _)]
  rfl

def eS (ι : Type*) [Fintype ι] (r : ℕ) : (Ix ι r → ℂ) ≃ᵐ (LoI ι r → ℂ) × (UpI ι r → ℂ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma eS_symm_apply (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (i : Ix ι r) :
    (eS ι r).symm (x, y) i = if h : i.2.2 < i.2.1 then x ⟨i, h⟩ else y ⟨i, h⟩ := rfl

def Nmat (x : LoI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : b < a then x ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h : b < a`. Simplify using `[sl, Nmat, eS_symm_apply, Matrix.one_apply, h, h.ne']`. Simplify using `[sl, Nmat, eS_symm_apply, Matrix.one_apply, h]`.
-/
lemma one_add_sl_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (τ : ι) :
    1 + sl ((eS ι r).symm (x, y)) τ = Nmat x τ := by
  ext a b
  by_cases h : b < a
  · simp [sl, Nmat, eS_symm_apply, Matrix.one_apply, h, h.ne']
  · simp [sl, Nmat, eS_symm_apply, Matrix.one_apply, h]

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `by_cases h : b < a <;> simp [up, Umat, eS_symm_apply, h]`.
-/
lemma up_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (τ : ι) : up ((eS ι r).symm (x, y)) τ = Umat y τ := by
  ext a b
  by_cases h : b < a <;> simp [up, Umat, eS_symm_apply, h]

/- English proof (translation)
Unfold `jac jacU`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i.2.2 < i.2.1 <;> simp [h, eS_symm_apply, dI]`.
-/
lemma jac_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) : jac ((eS ι r).symm (x, y)) = jacU y := by
  unfold jac jacU
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h, eS_symm_apply, dI]

/- English proof (translation)
Simplify using `[sS, eS_symm_apply, dI]`.
-/
lemma mem_sS_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) :
    (eS ι r).symm (x, y) ∈ sS ι r ↔ ∀ τ b, y (dI τ b) ≠ 0 := by
  simp [sS, eS_symm_apply, dI]

/- English proof (translation)
Unfold `Mt`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, lu]`. Rewrite using `[one_add_sl_eS, up_eS]`.
-/
lemma Mt_lu_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (τ : ι) :
    Mt (lu ((eS ι r).symm (x, y))) τ = Nmat x τ * Umat y τ := by
  unfold Mt
  ext a b
  simp only [Matrix.of_apply, lu]
  rw [one_add_sl_eS, up_eS]

/- English proof (translation)
Establish `hmp : MeasurePreserving (eS ι r) volume volume` using `volume_preserving_piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)`. Use `set F : (Ix ι r → ℂ) → ENNReal := (sS ι r).indicator (fun w => ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w)) with hF`. Establish `hFm : Measurable F` using `((Complex.continuous_normSq.comp continuous_jac).measurable.ennreal_ofReal.mul (hg.comp continuous_lu.measurable)).indicator measurableSet_sS`. Rewrite using `[lintegral_lu]`. Use `first`.

Consider the case `rw [← lintegral_indicator measurableSet_sS]`. Consider the case `rw [← lintegral_indicator _ measurableSet_sS]`. Rewrite using `[← hmp.symm.lintegral_comp_emb (eS ι r).symm.measurableEmbedding, Measure.volume_eq_prod]`. Use `(lintegral_prod _ ?_).trans ?_` and prove the remaining obligations. Conclude with `(hFm.comp (eS ι r).symm.measurable).aemeasurable`.

Use `lintegral_congr fun x => lintegral_congr fun y => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∀ τ b, y (dI τ b) ≠ 0`. Rewrite using `[if_pos h, Set.indicator_of_mem ((mem_sS_eS x y).2 h)]`. Simplify using `only [jac_eS]`. Rewrite using `[if_neg h] first`.

Consider the case `exact Set.indicator_of_notMem (fun hm => h ((mem_sS_eS x y).1 hm)) _`. Consider the case `exact Set.indicator_of_not_mem (fun hm => h ((mem_sS_eS x y).1 hm)) _`.
-/
theorem lintegral_flat {g : (Ix ι r → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v = ∫⁻ x, ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * g (lu ((eS ι r).symm (x, y))) else 0) := by
  have hmp : MeasurePreserving (eS ι r) volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)
  set F : (Ix ι r → ℂ) → ENNReal :=
    (sS ι r).indicator (fun w => ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w)) with hF
  have hFm : Measurable F :=
    ((Complex.continuous_normSq.comp continuous_jac).measurable.ennreal_ofReal.mul
      (hg.comp continuous_lu.measurable)).indicator measurableSet_sS
  rw [lintegral_lu]
  first
  | rw [← lintegral_indicator measurableSet_sS]
  | rw [← lintegral_indicator _ measurableSet_sS]
  rw [← hmp.symm.lintegral_comp_emb (eS ι r).symm.measurableEmbedding, Measure.volume_eq_prod]
  refine (lintegral_prod _ ?_).trans ?_
  · exact (hFm.comp (eS ι r).symm.measurable).aemeasurable
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  by_cases h : ∀ τ b, y (dI τ b) ≠ 0
  · rw [if_pos h, Set.indicator_of_mem ((mem_sS_eS x y).2 h)]
    simp only [jac_eS]
  · rw [if_neg h]
    first
    | exact Set.indicator_of_notMem (fun hm => h ((mem_sS_eS x y).1 hm)) _
    | exact Set.indicator_of_not_mem (fun hm => h ((mem_sS_eS x y).1 hm)) _
