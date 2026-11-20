import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

local instance instMSMat {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelMat {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

local instance instSCMat {m n : Type*} [Fintype m] [Fintype n] : SecondCountableTopology (Matrix m n ℂ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℂ))

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]`. Conclude with `(continuous_id.matrix_det.measurable.inv).mul (continuous_id.matrix_adjugate.matrix_elem i j).measurable`.
-/
theorem meas_inv {n : Type*} [Fintype n] [DecidableEq n] : Measurable fun A : Matrix n n ℂ => A⁻¹ := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

/- English proof (translation)
Establish `hB : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => M.toBlocks₂₂` using `(show Continuous fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => (M.toBlocks₂₂ : Matrix (Fin q) (Fin q) ℂ) from continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)).measurable`. Establish `hBi` using `(meas_inv (n := Fin q)).comp hB`. Unfold `Yb`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`.

Use `Finset.measurable_sum _ fun k _ => ?_` and prove the remaining obligations. Conclude with `(continuous_id.matrix_elem (Sum.inl i) (Sum.inr k)).measurable.mul ((continuous_id.matrix_elem k j).measurable.comp hBi)`.
-/
theorem meas_Yb {p q : ℕ} : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => Yb M := by
  have hB : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => M.toBlocks₂₂ :=
    (show Continuous fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
        (M.toBlocks₂₂ : Matrix (Fin q) (Fin q) ℂ) from
      continuous_pi fun i => continuous_pi fun j =>
        continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)).measurable
  have hBi := (meas_inv (n := Fin q)).comp hB
  unfold Yb
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (continuous_id.matrix_elem (Sum.inl i) (Sum.inr k)).measurable.mul
    ((continuous_id.matrix_elem k j).measurable.comp hBi)

/- English proof (translation)
Unfold `dpow`. Conclude with `(Complex.continuous_re.comp ((continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s`.
-/
theorem meas_dpow {p q : ℕ} (s : ℝ) : Measurable fun Z : Matrix (Fin p) (Fin q) ℂ => dpow Z s := by
  unfold dpow
  exact (Complex.continuous_re.comp ((continuous_const.sub
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
The claim follows from `continuous_apply τ`.
-/
theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ

/- English proof (translation)
Unfold `Mx tl`. Conclude with `(continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _`.
-/
theorem cont_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) : Continuous fun x => Mx X x0 x τ := by
  unfold Mx tl
  exact (continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _

/- English proof (translation)
Unfold `kap`. Conclude with `Finset.measurable_prod _ fun τ _ => (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)`.
-/
theorem meas_kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kap X x0 bb) := by
  unfold kap
  exact Finset.measurable_prod _ fun τ _ =>
    (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)

/- English proof (translation)
Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Use `show Continuous fun x : Frame X.Ψ r => ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)`. Conclude with `continuous_const.matrix_mul (cont_mat X τ)`.
-/
theorem cont_lact (X : Data E r) (γ : GL (Fin r) E) : Continuous (lact (Ψ := X.Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : Frame X.Ψ r =>
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  exact continuous_const.matrix_mul (cont_mat X τ)

/- English proof (translation)
Establish `h : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩ ⋂ a, ⋂ c, {b : Frame X.Ψ r | c < a → b τ a c = 0})`. Use extensionality with `b`. Simplify using `[Bor]`. Rewrite using `[h]`. Use `MeasurableSet.iInter fun τ => ?_` and prove the remaining obligations.

Use `MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)` and prove the remaining obligations. Conclude with `(isOpen_ne_fun (cont_mat X τ).matrix_det continuous_const).measurableSet`. Distinguish the cases in `hca : c < a`. Simplify using `only [hca, true_implies]`. Conclude with `(isClosed_eq (by fun_prop) continuous_const).measurableSet`.

Simplify using `[hca]`.
-/
theorem meas_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a, ⋂ c, {b : Frame X.Ψ r | c < a → b τ a c = 0}) := by
    ext b
    simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · exact (isOpen_ne_fun (cont_mat X τ).matrix_det continuous_const).measurableSet
  · by_cases hca : c < a
    · simp only [hca, true_implies]
      exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
    · simp [hca]

local instance instPolishFrame (X : Data E r) : PolishSpace (Frame X.Ψ r) where

def Sset (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun pr : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 pr.1) pr.2) '' (FF ×ˢ Bor X.Ψ r)

/- English proof (translation)
Establish `: PolishSpace (V (nd X) × Frame X.Ψ r)` using `{}`. Use `MeasurableSet.image_of_continuousOn_injOn (hFF.prod (meas_Bor X)) ?_ ?_` and prove the remaining obligations. Use `Continuous.continuousOn (continuous_pi fun τ => ?_)` and prove the remaining obligations. Conclude with `((cont_mat X τ).comp ((cont_cpt X x0).comp continuous_fst)).matrix_mul ((cont_mat X τ).comp continuous_snd)`. Introduce and unpack `⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h`.

Take `⟨e1, e2⟩` from `cpt_inj X ho hb hb' h`. Conclude with `Prod.ext e1 e2`.
-/
theorem meas_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) : MeasurableSet (Sset X x0 FF) := by
  have : PolishSpace (V (nd X) × Frame X.Ψ r) := {}
  refine MeasurableSet.image_of_continuousOn_injOn (hFF.prod (meas_Bor X)) ?_ ?_
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact ((cont_mat X τ).comp ((cont_cpt X x0).comp continuous_fst)).matrix_mul
      ((cont_mat X τ).comp continuous_snd)
  · rintro ⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h
    obtain ⟨e1, e2⟩ := cpt_inj X ho hb hb' h
    exact Prod.ext e1 e2

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)`.
-/
private lemma rmul_rmul_eq_rmul_rmul (X : Data E r) (x b c : Frame X.Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)

/- English proof (translation)
Introduce `τ`. Establish `hm : mat (rmul b c) τ = mat b τ * mat c τ` using `rfl`. Use `⟨?_, fun a d hda => ?_⟩` and prove the remaining obligations. Rewrite using `[hm, Matrix.det_mul]`. Conclude with `mul_ne_zero (hb τ).1 (hc τ).1`.

Establish `h1 : (mat b τ).BlockTriangular id` using `fun i j h => (hb τ).2 i j h`. Establish `h2 : (mat c τ).BlockTriangular id` using `fun i j h => (hc τ).2 i j h`. Conclude with `(h1.mul h2) hda`.
-/
private lemma bor_rmul_mem (X : Data E r) {b c : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hc : c ∈ Bor X.Ψ r) : rmul b c ∈ Bor X.Ψ r := by
  intro τ
  have hm : mat (rmul b c) τ = mat b τ * mat c τ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
    have h2 : (mat c τ).BlockTriangular id := fun i j h => (hc τ).2 i j h
    exact (h1.mul h2) hda

/- English proof (translation)
Introduce `τ`. Establish `hu : IsUnit (mat b τ).det` using `isUnit_iff_ne_zero.mpr (hb τ).1`. Establish `hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹` using `rfl`. Use `⟨?_, fun a d hda => ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`.

Conclude with `(Matrix.isUnit_nonsing_inv_det _ hu).ne_zero`. Use `letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu`. Establish `h1 : (mat b τ).BlockTriangular id` using `fun i j h => (hb τ).2 i j h`. Conclude with `(Matrix.blockTriangular_inv_of_blockTriangular h1) hda`.
-/
private lemma inv_mat_mem_bor (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  have hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
  have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular h1) hda

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hu : IsUnit (mat b τ).det` using `isUnit_iff_ne_zero.mpr (hb τ).1`. Use `show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
private lemma rmul_rmul_inv_mat (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (y : Frame X.Ψ r) :
    rmul (rmul y b) (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩`. Use `⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at h ⊢`. Conclude with `(rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))`.

Introduce and unpack `⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩`. Use `⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩` and prove the remaining obligations. Simplify using `only at h ⊢`. Conclude with `(rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)`.
-/
theorem rmul_mem_S (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans
      ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z', b'⟩, ⟨hz', hb'⟩, h⟩`. Simplify using `only at h`. Rewrite `h` using `[← ExtFPf.rmul_oneF X (cpt X x0 z)]`. Rewrite using `[← (cpt_inj X ho hb' (ExtFPf.oneF_mem X) h).1]` and apply the resulting hypothesis.

Introduce `hz`. Conclude with `⟨⟨z, ExtFPf.oneF X⟩, ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩`.
-/
theorem cpt_mem_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (z : V (nd X)) :
    cpt X x0 z ∈ Sset X x0 FF ↔ z ∈ FF := by
  constructor
  · rintro ⟨⟨z', b'⟩, ⟨hz', hb'⟩, h⟩
    simp only at h
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rwa [← (cpt_inj X ho hb' (ExtFPf.oneF_mem X) h).1]
  · intro hz
    exact ⟨⟨z, ExtFPf.oneF X⟩, ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ`. Conclude with `(Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm`.
-/
theorem lact_rmul' (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
