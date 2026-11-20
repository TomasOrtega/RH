import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.FlagGS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Establish `hs0 : ∀ a, s a ≠ 0` using `fun a h0 => by simpa [h0] using hs a`. Establish `hss : diagonal s * diagonal s = (1 : Matrix (Fin r) (Fin r) ℂ)`. Rewrite using `[diagonal_mul_diagonal]`. Simplify using `[hs]`. Establish `h1 : (diagonal s * bᵀ * diagonal s) * b.map (starRingEnd ℂ) = 1`.

Rewrite using `[Matrix.mul_assoc (diagonal s), Matrix.mul_assoc (diagonal s), h, hss]`. Establish `hc : (b.map (starRingEnd ℂ)).BlockTriangular id` using `fun a c hca => by`. Rewrite using `[Matrix.map_apply, hb hca, map_zero]`. Use `letI : Invertible (b.map (starRingEnd ℂ)) := invertibleOfLeftInverse _ _ h1`. Establish `hinv` using `Matrix.blockTriangular_inv_of_blockTriangular hc`.

Rewrite `hinv` using `[Matrix.inv_eq_left_inv h1]`. Establish `hoff : ∀ a c, a ≠ c → b a c = 0`. Introduce `a c hac`. Break down `lt_or_gt_of_ne hac with hlt | hlt` into its components or cases. Use `hinv (i := c) (j := a) hlt` as an intermediate fact.

Rewrite `this` using `[mul_diagonal, diagonal_mul, transpose_apply]`. Simplify `this` using `[hs0]`. Conclude with `hb hlt`. Establish `hd : b = diagonal fun a => b a a`. Use extensionality with `a c`.

Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[diagonal_apply_ne _ hac, hoff a c hac]`. Establish `hn : ∀ a, ‖b a a‖ = 1`.

Introduce `a`. Establish `h2` using `congrFun (congrFun h a) a`. Rewrite `h2` using `[hd, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]`. Simplify using `only [diagonal_apply_eq] at h2`. Establish `h3 : b a a * starRingEnd ℂ (b a a) = 1`.

Apply `mul_left_cancel₀ (hs0 a)` to reduce the goal to its premises. Take the linear combination `h2`. Establish `h4` using `congrArg norm h3`. Rewrite `h4` using `[norm_mul, Complex.norm_conj, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (b a a)]`.

Use `⟨fun a => Complex.arg (b a a), ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [diagonal_apply_eq]`.

Use `Complex.norm_mul_exp_arg_mul_I (b a a)` as an intermediate fact. Rewrite `this` using `[hn a]`. Simplify using `using this.symm`.
-/
theorem diag_of_upper {r : ℕ} (s : Fin r → ℂ) (hs : ∀ a, s a * s a = 1) (b : Matrix (Fin r) (Fin r) ℂ)
    (hb : b.BlockTriangular id) (h : bᵀ * diagonal s * b.map (starRingEnd ℂ) = diagonal s) :
    ∃ t : Fin r → ℝ, b = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
  have hs0 : ∀ a, s a ≠ 0 := fun a h0 => by simpa [h0] using hs a
  have hss : diagonal s * diagonal s = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [diagonal_mul_diagonal]; simp [hs]
  have h1 : (diagonal s * bᵀ * diagonal s) * b.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.mul_assoc (diagonal s), Matrix.mul_assoc (diagonal s), h, hss]
  have hc : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    rw [Matrix.map_apply, hb hca, map_zero]
  letI : Invertible (b.map (starRingEnd ℂ)) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hc
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have hoff : ∀ a c, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · have := hinv (i := c) (j := a) hlt
      rw [mul_diagonal, diagonal_mul, transpose_apply] at this
      simpa [hs0] using this
    · exact hb hlt
  have hd : b = diagonal fun a => b a a := by
    ext a c
    by_cases hac : a = c
    · subst hac; simp
    · rw [diagonal_apply_ne _ hac, hoff a c hac]
  have hn : ∀ a, ‖b a a‖ = 1 := by
    intro a
    have h2 := congrFun (congrFun h a) a
    rw [hd, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal] at h2
    simp only [diagonal_apply_eq] at h2
    have h3 : b a a * starRingEnd ℂ (b a a) = 1 := by
      apply mul_left_cancel₀ (hs0 a)
      linear_combination h2
    have h4 := congrArg norm h3
    rw [norm_mul, Complex.norm_conj, norm_one] at h4
    nlinarith [norm_nonneg (b a a)]
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  rw [hd]
  congr 1
  funext a
  simp only [diagonal_apply_eq]
  have := Complex.norm_mul_exp_arg_mul_I (b a a)
  rw [hn a] at this
  simpa using this.symm

/- English proof (translation)
Establish `hu : IsUnit H.det` using `Matrix.isUnit_det_of_left_inverse hH`. Establish `hu' : IsUnit H` using `(isUnit_iff_isUnit_det H).2 hu`. Establish `e : Zᴴ = H * (-Z) * H⁻¹`. Establish `h1 : Zᴴ * H = -(H * Z)` using `eq_neg_of_add_eq_zero_left hZ`. Rewrite using `[mul_neg, ← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]`.

Rewrite using `[← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
theorem exp_keeps {r : ℕ} {H Z : Matrix (Fin r) (Fin r) ℂ} (hH : H * H = 1) (hZ : Zᴴ * H + H * Z = 0) :
    (NormedSpace.exp Z)ᴴ * H * NormedSpace.exp Z = H := by
  have hu : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hH
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : Zᴴ = H * (-Z) * H⁻¹ := by
    have h1 : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left hZ
    rw [mul_neg, ← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

/- English proof (translation)
Establish `h2` using `congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h`. Simplify using `only [Matrix.map_mul, diagonal_map (map_zero (starRingEnd ℂ)), Complex.conj_ofReal] at h2`. Establish `e : gᴴ.map (starRingEnd ℂ) = gᵀ`. Use extensionality with `a c`. Simplify using `[conjTranspose_apply]`.

Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem conj_keeps {r : ℕ} (s : Fin r → ℝ) (g : Matrix (Fin r) (Fin r) ℂ)
    (h : gᴴ * diagonal (fun a => (s a : ℂ)) * g = diagonal fun a => (s a : ℂ)) :
    gᵀ * diagonal (fun a => (s a : ℂ)) * g.map (starRingEnd ℂ) = diagonal fun a => (s a : ℂ) := by
  have h2 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, diagonal_map (map_zero (starRingEnd ℂ)), Complex.conj_ofReal] at h2
  have e : gᴴ.map (starRingEnd ℂ) = gᵀ := by
    ext a c; simp [conjTranspose_apply]
  rwa [e] at h2

/- English proof (translation)
Introduce `E _ _ _ r X`. Establish `hdom : ∀ y, IsUnitFr X y → y ∈ X.dom` using `fun y hy => ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hy`. Use `⟨hdom, fun x hx => ?_, fun y hy b hb hyb => ?_, fun x hx b hb => ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun y hy γ hγ τ => ?_, fun y hy Z hZ τ => ?_, fun la P y hy b hb hP => ?_⟩` and prove the remaining obligations. Establish `hb` using `FrameDegreeData.bOf_mem X hx`. Use `⟨rmul x (FrameDegreeData.bOf X x), FrameDegreeData.ortho_bOf X hx, fun τ => ((mat (FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det` using `isUnit_iff_ne_zero.2 (hb τ).1`. Use `letI := Matrix.invertibleOfIsUnitDet _ hu`. Use `⟨?_, fun a c hca => Matrix.blockTriangular_inv_of_blockTriangular (FrameDegreeData.upper_of_bor X hb τ) hca⟩` and prove the remaining obligations. Conclude with `(Matrix.isUnit_nonsing_inv_det _ hu).ne_zero`. Use function extensionality and compare the values at `τ`.

Establish `hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det` using `isUnit_iff_ne_zero.2 (hb τ).1`. Conclude with `(Matrix.mul_nonsing_inv_cancel_right _ (mat x τ) hu).symm`. Establish `h : ∀ τ : X.Ψ, ∃ t : Fin r → ℝ, mat b τ = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)`. Introduce `τ`. Establish `h1` using `hyb τ`.

Rewrite `h1` using `[show mat (rmul y b) τ = mat y τ * mat b τ from rfl, FrameDegreeData.gram_mul, hy τ]`. Conclude with `diag_of_upper _ (fun a => sgn_mul_self _ _) _ (FrameDegreeData.upper_of_bor X hb τ) h1`. Use `choose t ht using h`. Conclude with `⟨t, funext fun τ => ht τ⟩`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]`.

Conclude with `hy τ`. Rewrite using `[show mat (rmul y (expFr Z)) τ = mat y τ * NormedSpace.exp (mat Z τ) from rfl, FrameDegreeData.gram_mul, hy τ]`. Use `conj_keeps _ _ (exp_keeps ?_ (hZ τ))` and prove the remaining obligations. Rewrite using `[diagonal_mul_diagonal]`. Simplify using `only [sgn_mul_self]`.

Conclude with `diagonal_one`. Establish `hx` using `hdom y hy`. Unfold `Data.pnorm`. Rewrite using `[hP, norm_mul]`. Establish `hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i`.

Unfold `bchar`. Simplify using `only [norm_prod, norm_zpow]`. Rewrite using `[hbc, mul_comm (∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i) ‖P y‖, mul_assoc, ← Finset.prod_mul_distrib]`. Use `conv_rhs => rw [← mul_one ‖P y‖]`. Use `congr 1`.

Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[FrameDegreeData.ratio_rmul X y hx hb τ i, FrameDegreeData.factor_eq _ _ (norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ i)) (norm_nonneg _), norm_div, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_ …`.
-/
theorem gram_schmidt_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  intro E _ _ _ r X
  have hdom : ∀ y, IsUnitFr X y → y ∈ X.dom := fun y hy => ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hy
  refine ⟨hdom, fun x hx => ?_, fun y hy b hb hyb => ?_,
    fun x hx b hb => ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun y hy γ hγ τ => ?_, fun y hy Z hZ τ => ?_,
    fun la P y hy b hb hP => ?_⟩
  · have hb := FrameDegreeData.bOf_mem X hx
    refine ⟨rmul x (FrameDegreeData.bOf X x), FrameDegreeData.ortho_bOf X hx, fun τ => ((mat (FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ),
      fun τ => ?_, ?_⟩
    · have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      letI := Matrix.invertibleOfIsUnitDet _ hu
      refine ⟨?_, fun a c hca => Matrix.blockTriangular_inv_of_blockTriangular (FrameDegreeData.upper_of_bor X hb τ) hca⟩
      exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
    · funext τ
      have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      exact (Matrix.mul_nonsing_inv_cancel_right _ (mat x τ) hu).symm
  · have h : ∀ τ : X.Ψ, ∃ t : Fin r → ℝ, mat b τ = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
      intro τ
      have h1 := hyb τ
      rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, FrameDegreeData.gram_mul, hy τ] at h1
      exact diag_of_upper _ (fun a => sgn_mul_self _ _) _ (FrameDegreeData.upper_of_bor X hb τ) h1
    choose t ht using h
    exact ⟨t, funext fun τ => ht τ⟩
  · rw [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]
    exact hy τ
  · rw [show mat (rmul y (expFr Z)) τ = mat y τ * NormedSpace.exp (mat Z τ) from rfl, FrameDegreeData.gram_mul, hy τ]
    refine conj_keeps _ _ (exp_keeps ?_ (hZ τ))
    rw [diagonal_mul_diagonal]
    simp only [sgn_mul_self]
    exact diagonal_one
  · have hx := hdom y hy
    unfold Data.pnorm
    rw [hP, norm_mul]
    have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
      unfold bchar
      simp only [norm_prod, norm_zpow]
    rw [hbc, mul_comm (∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i) ‖P y‖, mul_assoc, ← Finset.prod_mul_distrib]
    conv_rhs => rw [← mul_one ‖P y‖]
    congr 1
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [FrameDegreeData.ratio_rmul X y hx hb τ i,
      FrameDegreeData.factor_eq _ _ (norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ i)) (norm_nonneg _), norm_div,
      ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy,
      div_one, Real.one_rpow]

end GlobalTheory.FlagGS
