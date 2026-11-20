import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfJ

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def NF (x : LoI X.Ψ r → ℂ) : Frame X.Ψ r := fun τ => Nmat x τ

def densY (y : Frame X.Ψ r) : ℝ := ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ (-2 : ℤ)

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : a < b` using `OrderDual.toDual_lt_toDual.mp hab`. Establish `h1 : ¬ b < a` using `not_lt.mpr hab'.le`. Establish `h2 : a ≠ b` using `hab'.ne`. Use `first`.

Consider the case `simp [Nmat, h1, h2]`. Consider the case `(unfold Nmat; rw [Matrix.of_apply, dif_neg h1]; simp [h2, Ne.symm h2])`.
-/
lemma Nmat_low (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) : (Nmat x τ).BlockTriangular OrderDual.toDual := by
  intro a b hab
  have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
  have h1 : ¬ b < a := not_lt.mpr hab'.le
  have h2 : a ≠ b := hab'.ne
  first
  | simp [Nmat, h1, h2]
  | (unfold Nmat; rw [Matrix.of_apply, dif_neg h1]; simp [h2, Ne.symm h2])

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular _ (Nmat_low X x τ)]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Unfold `Nmat`. Rewrite using `[Matrix.of_apply, dif_neg (lt_irrefl a)]`. Simplify using the standard rewrite rules.
-/
lemma det_Nmat (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) : (Nmat x τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (Nmat_low X x τ)]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold Nmat
  rw [Matrix.of_apply, dif_neg (lt_irrefl a)]
  simp

/- English proof (translation)
Establish `e : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ)`. Use extensionality with `a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Use `first`. Consider the case `exact Finset.sum_comm`.

Consider the case `rw [Finset.sum_comm]`. Establish `hc : (M.map (starRingEnd ℂ)).det = (starRingEnd ℂ) M.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]`.
-/
private theorem det_gram' (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M).det = M.det * (X.Gm.map τ.1).det * (starRingEnd ℂ) M.det := by
  have e : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    first
    | exact Finset.sum_comm
    | rw [Finset.sum_comm]
  have hc : (M.map (starRingEnd ℂ)).det = (starRingEnd ℂ) M.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (hx0 τ)`. Rewrite `h` using `[det_gram', Matrix.det_diagonal]`. Establish `hn : ‖(mat x0 τ).det * (X.Gm.map τ.1).det * (starRingEnd ℂ) (mat x0 τ).det‖ = 1`. Rewrite using `[h, norm_prod]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hn` using `[norm_mul, norm_mul, Complex.norm_conj]`. Then use the resulting hypothesis.
-/
private theorem norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    ‖(mat x0 τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x0 τ).det‖ = 1 := by
  have h := congrArg Matrix.det (hx0 τ)
  rw [det_gram', Matrix.det_diagonal] at h
  have hn : ‖(mat x0 τ).det * (X.Gm.map τ.1).det * (starRingEnd ℂ) (mat x0 τ).det‖ = 1 := by
    rw [h, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sgn
    split_ifs <;> simp
  rwa [norm_mul, norm_mul, Complex.norm_conj] at hn

/- English proof (translation)
Establish `hl : ∀ M : Matrix (Fin r) (Fin r) ℂ, lminor M (Fin.last r) = M.det`. Introduce `M`. Unfold `lminor`. Use `first`. Consider the case `rfl`.

Consider the case `(congr 1)`. Consider the case `simp`. Establish `hdm : (mat (rmul x0 (NF X x)) τ).det = (mat x0 τ).det` using `by show (mat x0 τ * Nmat x τ).det = _`. Rewrite using `[Matrix.det_mul, det_Nmat, mul_one]`. Use `show ‖lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (rmul x0 (NF X x)) τ)) (Fin.last r)‖ = 1`.

Rewrite using `[hl, det_gram', hdm, norm_mul, norm_mul, Complex.norm_conj]`. Conclude with `norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ`.
-/
lemma norm_dmin_last {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) :
    ‖dmin X.Gm (rmul x0 (NF X x)) τ (Fin.last r)‖ = 1 := by
  have hl : ∀ M : Matrix (Fin r) (Fin r) ℂ, lminor M (Fin.last r) = M.det := by
    intro M
    unfold lminor
    first
    | rfl
    | (congr 1)
    | simp
  have hdm : (mat (rmul x0 (NF X x)) τ).det = (mat x0 τ).det := by
    show (mat x0 τ * Nmat x τ).det = _
    rw [Matrix.det_mul, det_Nmat, mul_one]
  show ‖lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (rmul x0 (NF X x)) τ)) (Fin.last r)‖ = 1
  rw [hl, det_gram', hdm, norm_mul, norm_mul, Complex.norm_conj]
  exact norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ

/- English proof (translation)
Rewrite using `[Complex.normSq_eq_norm_sq, ← norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma normSq_det_orthogonalFrame {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    Complex.normSq (mat x0 τ).det * ‖(X.Gm.map τ.1).det‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq, ← norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ]
  ring

def gI (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ENNReal) (v : Ix X.Ψ r → ℂ) : ENNReal :=
  φ (rmul x0 (uf X v)) * Wf X (rmul x0 (uf X v))

def GLo (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ENNReal) (x : LoI X.Ψ r → ℂ) : ENNReal :=
  if rmul x0 (NF X x) ∈ X.dom then φ (rmul x0 (NF X x)) * ENNReal.ofReal (densY X (rmul x0 (NF X x))) else 0

/- English proof (translation)
Establish `h1 : ∀ τ : X.Ψ, 1 + sl ((eS X.Ψ r).symm (x, y)) τ = Nmat x τ`. Introduce `τ`. Use extensionality with `a b`. Distinguish the cases in `h : b < a`. Establish `hab : a ≠ b` using `ne_of_gt h first`.

Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]`. Use `first`. Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]`.

Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]`. Establish `h2 : ∀ τ : X.Ψ, up ((eS X.Ψ r).symm (x, y)) τ = Umat y τ`. Introduce `τ`. Use extensionality with `a b`.

Distinguish the cases in `h : b < a`. Use `first`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]`.

Use `first`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]`. Consider the case `simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]`. Use function extensionality and compare the values at `τ a b`.

Use `show ((1 + sl ((eS X.Ψ r).symm (x, y)) τ) * up ((eS X.Ψ r).symm (x, y)) τ) a b = (Nmat x τ * Umat y τ) a b`. Rewrite using `[h1, h2]`.
-/
lemma uf_lu_eS (x : LoI X.Ψ r → ℂ) (y : UpI X.Ψ r → ℂ) :
    uf X (lu ((eS X.Ψ r).symm (x, y))) = rmul (NF X x) (UF X y) := by
  have h1 : ∀ τ : X.Ψ, 1 + sl ((eS X.Ψ r).symm (x, y)) τ = Nmat x τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · have hab : a ≠ b := ne_of_gt h
      first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
    · first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
  have h2 : ∀ τ : X.Ψ, up ((eS X.Ψ r).symm (x, y)) τ = Umat y τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
  funext τ a b
  show ((1 + sl ((eS X.Ψ r).symm (x, y)) τ) * up ((eS X.Ψ r).symm (x, y)) τ) a b =
    (Nmat x τ * Umat y τ) a b
  rw [h1, h2]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)).symm`.
-/
lemma rmul_assoc' (x b c : Frame X.Ψ r) : rmul x (rmul b c) = rmul (rmul x b) c := by
  funext τ
  exact (Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)).symm

/- English proof (translation)
Unfold `uf`. Use `first`. Consider the case `fun_prop`. Consider the case `exact continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => continuous_apply _`.
-/
lemma continuous_uf : Continuous (uf X) := by
  unfold uf
  first
  | fun_prop
  | exact continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => continuous_apply _

/- English proof (translation)
Unfold `densY`. Rewrite using `[← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `first`. Consider the case `simp only [_root_.zpow_neg, zpow_ofNat]`. Consider the case `simp [_root_.zpow_neg]`. Consider the case `norm_num [_root_.zpow_neg]`.
-/
lemma densY_eq {y : Frame X.Ψ r} :
    densY X y = (∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2)⁻¹ := by
  unfold densY
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  first
  | simp only [_root_.zpow_neg, zpow_ofNat]
  | simp [_root_.zpow_neg]
  | norm_num [_root_.zpow_neg]

/- English proof (translation)
Use `set Y := rmul x0 (NF X x) with hYd`. Establish `hrw : ∀ y, gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) = φ (rmul Y (UF X y)) * Wf X (rmul Y (UF X y))`. Introduce `y`. Simplify using `only [gI, uf_lu_eS, rmul_assoc', hYd]`. Distinguish the cases in `hY : Y ∈ X.dom`.

Establish `hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) = φ Y * (ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y))`. Introduce `y`. Use `split_ifs with hd`. Rewrite using `[hrw, hφ Y hY _ (UF_mem X hd), Wf_rmul_UF X hY hd]`. Expand and normalize the polynomial expressions, which then agree.

Use `push_neg at hd`. Take `⟨τ, b, hb⟩` from `hd`. Establish `hC : Lβ (β0 X Y) y ∉ Cy X.Ψ r` using `fun hC => by`. Use `((hC (dI τ b)).1 rfl).1` as an intermediate fact. Rewrite `this` using `[Lβ_diag _ (β0_upper X hY) y τ b, hb, mul_zero, norm_zero]`.

Evaluate the numerical expressions using `at this`. Rewrite using `[Set.indicator_of_notMem hC]`. Simplify using the standard rewrite rules. Establish `hmeas : Measurable fun y : UpI X.Ψ r → ℂ => ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y)` using `measurable_normSq_jacU.mul ((measurable_one.indicator measurableSet_Cy).comp (LinearMap.continuous_of_finiteDimensional (Lβ (β0 X Y))).measurable)`. Establish `hdiag : ∀ τ b, β0 X Y τ b b ≠ 0` using `fun τ b h0 => by`.

Use `normSq_β0_diag X hY τ b` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `(abs_re_pos X hY τ b).ne this`. Rewrite using `[lintegral_congr hpt, lintegral_const_mul _ hmeas, lintegral_upper _ (β0_upper X hY) hdiag, exponent_identity X hY (norm_dmin_last X hx0 x), GLo, if_pos hY, densY_eq, mul_assoc]`. Establish `hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) = 0`.

Introduce `y`. Use `split_ifs with hd`. Rewrite using `[hrw, Wf_rmul_not_dom X hY (UF_mem X hd), mul_zero, mul_zero]`. Both sides reduce to the same expression. Rewrite using `[lintegral_congr hpt, lintegral_zero, GLo, if_neg hY, zero_mul]`.
-/
theorem inner_eq {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {φ : Frame X.Ψ r → ENNReal}
    (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) =
      GLo X x0 φ x * K0 X.Ψ r := by
  set Y := rmul x0 (NF X x) with hYd
  have hrw : ∀ y, gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) = φ (rmul Y (UF X y)) * Wf X (rmul Y (UF X y)) := by
    intro y; simp only [gI, uf_lu_eS, rmul_assoc', hYd]
  by_cases hY : Y ∈ X.dom
  · have hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
        ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) =
        φ Y * (ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y)) := by
      intro y
      split_ifs with hd
      · rw [hrw, hφ Y hY _ (UF_mem X hd), Wf_rmul_UF X hY hd]; ring
      · push_neg at hd
        obtain ⟨τ, b, hb⟩ := hd
        have hC : Lβ (β0 X Y) y ∉ Cy X.Ψ r := fun hC => by
          have := ((hC (dI τ b)).1 rfl).1
          rw [Lβ_diag _ (β0_upper X hY) y τ b, hb, mul_zero, norm_zero] at this
          norm_num at this
        rw [Set.indicator_of_notMem hC]; simp
    have hmeas : Measurable fun y : UpI X.Ψ r → ℂ =>
        ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y) :=
      measurable_normSq_jacU.mul ((measurable_one.indicator measurableSet_Cy).comp
        (LinearMap.continuous_of_finiteDimensional (Lβ (β0 X Y))).measurable)
    have hdiag : ∀ τ b, β0 X Y τ b b ≠ 0 := fun τ b h0 => by
      have := normSq_β0_diag X hY τ b
      rw [h0, map_zero] at this
      exact (abs_re_pos X hY τ b).ne this
    rw [lintegral_congr hpt, lintegral_const_mul _ hmeas, lintegral_upper _ (β0_upper X hY) hdiag,
      exponent_identity X hY (norm_dmin_last X hx0 x), GLo, if_pos hY, densY_eq, mul_assoc]
  · have hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
        ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) = 0 := by
      intro y
      split_ifs with hd
      · rw [hrw, Wf_rmul_not_dom X hY (UF_mem X hd), mul_zero, mul_zero]
      · rfl
    rw [lintegral_congr hpt, lintegral_zero, GLo, if_neg hY, zero_mul]

/- English proof (translation)
Establish `hF : Measurable fun v => φ (uf X v) * Wf X (uf X v)` using `(hφm.comp (continuous_uf X).measurable).mul ((measurable_Wf X).comp (continuous_uf X).measurable)`. Establish `hdet : ∀ τ, (mat x0 τ).det ≠ 0` using `fun τ h0 => by`. Use `normSq_det_orthogonalFrame X hx0 τ` as an intermediate fact. Rewrite `this` using `[h0, map_zero, zero_mul]`. Conclude with `zero_ne_one this`.

Establish `hg : Measurable (gI X x0 φ)`. Use `hF.comp (LinearMap.continuous_of_finiteDimensional (LA (fun τ => mat x0 τ))).measurable` as an intermediate fact. Conclude with `this`. Establish `h1` using `lintegral_flat hg`. Simplify using `only [inner_eq X hx0 hφ] at h1`.

Establish `h2 : ∫⁻ v, gI X x0 φ v = ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ * ∫⁻ v, φ (uf X v) * Wf X (uf X v)` using `lintegral_comp_LA (fun τ => mat x0 τ) hdet hF`. Rewrite using `[← lintegral_mul_const' _ _ (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne, ← h1, h2]`. Use `congr 2`. Rewrite using `[map_prod, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, ← inv_pow]`. Use `congr 1`. Use `normSq_det_orthogonalFrame X hx0 τ` as an intermediate fact. Conclude with `(eq_inv_of_mul_eq_one_right this).symm`.
-/
theorem core {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ)
    (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    (∫⁻ x, GLo X x0 φ x) * K0 X.Ψ r =
      ENNReal.ofReal (∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ r) * ∫⁻ v, φ (uf X v) * Wf X (uf X v) := by
  have hF : Measurable fun v => φ (uf X v) * Wf X (uf X v) :=
    (hφm.comp (continuous_uf X).measurable).mul ((measurable_Wf X).comp (continuous_uf X).measurable)
  have hdet : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ h0 => by
    have := normSq_det_orthogonalFrame X hx0 τ
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  have hg : Measurable (gI X x0 φ) := by
    have := hF.comp (LinearMap.continuous_of_finiteDimensional (LA (fun τ => mat x0 τ))).measurable
    exact this
  have h1 := lintegral_flat hg
  simp only [inner_eq X hx0 hφ] at h1
  have h2 : ∫⁻ v, gI X x0 φ v = ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ *
      ∫⁻ v, φ (uf X v) * Wf X (uf X v) := lintegral_comp_LA (fun τ => mat x0 τ) hdet hF
  rw [← lintegral_mul_const' _ _ (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne, ← h1, h2]
  congr 2
  rw [map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← inv_pow]
  congr 1
  have := normSq_det_orthogonalFrame X hx0 τ
  exact (eq_inv_of_mul_eq_one_right this).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
