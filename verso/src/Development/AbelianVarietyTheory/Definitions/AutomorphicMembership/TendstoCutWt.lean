import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianInterpolation

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad GlobalTheory.ShFam ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TrueGeo
open scoped ComplexOrder

namespace GlobalTheory.ShFam.MetsTest

/- English proof (translation)
Assemble the required witnesses or components as `⟨contDiff_cutoff.1.contDiffOn, fun y _ => cutoff_mem y, fun _ h => cutoff_of_le h.2, fun _ h => cutoff_of_ge h, contDiff_cutoff.2.contDiffOn⟩`.
-/
theorem isCutoff : GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation.IsCutoff cutoff :=
  ⟨contDiff_cutoff.1.contDiffOn, fun y _ => cutoff_mem y, fun _ h => cutoff_of_le h.2, fun _ h => cutoff_of_ge h,
    contDiff_cutoff.2.contDiffOn⟩

/- English proof (translation)
Establish `h1 : Tendsto (fun R : ℝ => r / R) atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop tendsto_id`. Establish `h2 : Tendsto (fun R : ℝ => (r / R) ^ κ) atTop (𝓝 0)`. Simplify `h1.rpow_const (p := κ) (.inr hκ.le)` using `[Real.zero_rpow hκ.ne']`. Establish `h3 : Tendsto (fun R : ℝ => 1 / (1 + (r / R) ^ κ)) atTop (𝓝 1)`. Simplify using `using (h2.const_add 1).inv₀ (by norm_num)`.

Use `h3.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop r] with R h4 h5`. Conclude with `(cutWt_of_le κ h4 hr (by nlinarith)).symm`.
-/
theorem tendsto_cutWt {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) : Tendsto (fun R => cutWt κ R r) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℝ => r / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun R : ℝ => (r / R) ^ κ) atTop (𝓝 0) := by
    simpa [Real.zero_rpow hκ.ne'] using h1.rpow_const (p := κ) (.inr hκ.le)
  have h3 : Tendsto (fun R : ℝ => 1 / (1 + (r / R) ^ κ)) atTop (𝓝 1) := by
    simpa using (h2.const_add 1).inv₀ (by norm_num)
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop r] with R h4 h5
  exact (cutWt_of_le κ h4 hr (by nlinarith)).symm

/- English proof (translation)
Rewrite using `[cutWt_of_le 0 hR hr h, Real.rpow_zero, one_add_one_eq_two]`.
-/
theorem cutWt_zero {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) : cutWt 0 R r = 1 / 2 := by
  rw [cutWt_of_le 0 hR hr h, Real.rpow_zero, one_add_one_eq_two]

/- English proof (translation)
Establish `h1` using `Real.rpow_pos_of_pos (div_pos hr (by linarith : 0 < R)) κ`. Rewrite using `[cutWt_of_le κ hR hr h]`. Conclude with `⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩`.
-/
theorem cutWt_mem_Ioo (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) : cutWt κ R r ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 := Real.rpow_pos_of_pos (div_pos hr (by linarith : 0 < R)) κ
  rw [cutWt_of_le κ hR hr h]
  exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

/- English proof (translation)
Use `set U := (LDL.lowerInv h)ᴴ with hU`. Establish `hT : ∀ a c, c < a → U a c = 0` using `fun a c hc => by simp [hU, LDL.lowerInv_triangular h hc]`. Establish `hu : IsUnit U.det`. Rewrite using `[hU, det_conjTranspose]`. Conclude with `(isUnit_det_of_invertible _).star`.

Establish `hd : ∀ a, U a a ≠ 0` using `fun a => by`. Rewrite `hu` using `[det_of_upperTriangular (M := U) fun _ _ h => hT _ _ h]`. Conclude with `Finset.prod_ne_zero_iff.1 hu.ne_zero a (Finset.mem_univ _)`. Establish `hD : Uᴴ * M * U = diagonal (LDL.diagEntries h)`. Rewrite using `[hU, conjTranspose_conjTranspose]`.

Conclude with `(LDL.diag_eq_lowerInv_conj h).symm`. Establish `hp : ∀ a, 0 < LDL.diagEntries h a` using `posDef_diagonal_iff.1 (hD ▸ h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hu)))`. Take `⟨d, hd0, hD⟩ : ∃ d : Fin m → ℝ, (∀ a, 0 < d a) ∧ Uᴴ * M * U = diagonal fun a => (d a : ℂ)` from `⟨fun a => (LDL.diagEntries h a).re, fun a => (Complex.pos_iff.1 (hp a)).1, hD.trans (congrArg _ (funext fun a => Complex.ext rfl (Complex.pos_iff.1 (hp a)).2.symm))⟩`. Establish `e1 (i) : d i = ‖U i i‖ ^ 2 * grSq M i` using `by rw [← grSq_tri M hT hd, hD, grSq_diagonal fun a => (hd0 a).ne']`. Establish `e0 : dualGram (diagonal fun a => (d a : ℂ)) = diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)`.

Rewrite using `[dualGram, Matrix.inv_eq_left_inv (B := diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)), diagonal_transpose]`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[← Complex.ofReal_mul, inv_mul_cancel₀ (hd0 a).ne']`.

Both sides reduce to the same expression. Establish `e2 : dualGram M = Uᵀᴴ * (diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)) * Uᵀ`. Establish `hut : IsUnit Uᵀ.det` using `by rwa [det_transpose]`. Rewrite using `[← e0, ← hD, dualGram_conj, transpose_nonsing_inv, Matrix.mul_assoc, nonsing_inv_mul_cancel_right _ _ hut, ← Matrix.mul_assoc, ← conjTranspose_mul, nonsing_inv_mul _ hut, conjTranspose_one, Matrix.one_mul]`. Establish `e3 : (dualGram M).submatrix Fin.rev Fin.rev = (Uᵀ.submatrix Fin.rev Fin.rev)ᴴ * (diagonal fun a : Fin m => (((d a.rev)⁻¹ : ℝ) : ℂ)) * Uᵀ.submatrix Fin.rev Fin.rev`.

Rewrite using `[e2, ← submatrix_mul_equiv _ _ _ Fin.revPerm, ← submatrix_mul_equiv _ _ _ Fin.revPerm, conjTranspose_submatrix]`. Use `congr 2`. Conclude with `submatrix_diagonal_equiv _ Fin.revPerm`. Rewrite using `[e3, grSq_tri _ (T := Uᵀ.submatrix Fin.rev Fin.rev) (fun a c hc => hT _ _ (Fin.rev_lt_rev.2 hc)) (fun a => hd _), grSq_diagonal (d := fun a => (d a.rev)⁻¹) fun a => inv_ne_zero (hd0 _).ne', e1]`. Use `norm_ne_zero_iff.2 (hd i.rev)` as an intermediate fact.

Simplify using `only [submatrix_apply, transpose_apply]`. Clear the denominators using the available nonvanishing facts.
-/
theorem grSq_dual_rev {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (i : Fin m) :
    grSq ((dualGram M).submatrix Fin.rev Fin.rev) i = (grSq M i.rev)⁻¹ := by
  set U := (LDL.lowerInv h)ᴴ with hU
  have hT : ∀ a c, c < a → U a c = 0 := fun a c hc => by simp [hU, LDL.lowerInv_triangular h hc]
  have hu : IsUnit U.det := by
    rw [hU, det_conjTranspose]; exact (isUnit_det_of_invertible _).star
  have hd : ∀ a, U a a ≠ 0 := fun a => by
    rw [det_of_upperTriangular (M := U) fun _ _ h => hT _ _ h] at hu
    exact Finset.prod_ne_zero_iff.1 hu.ne_zero a (Finset.mem_univ _)
  have hD : Uᴴ * M * U = diagonal (LDL.diagEntries h) := by
    rw [hU, conjTranspose_conjTranspose]; exact (LDL.diag_eq_lowerInv_conj h).symm
  have hp : ∀ a, 0 < LDL.diagEntries h a := posDef_diagonal_iff.1
    (hD ▸ h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hu)))
  obtain ⟨d, hd0, hD⟩ : ∃ d : Fin m → ℝ, (∀ a, 0 < d a) ∧ Uᴴ * M * U = diagonal fun a => (d a : ℂ) :=
    ⟨fun a => (LDL.diagEntries h a).re, fun a => (Complex.pos_iff.1 (hp a)).1, hD.trans (congrArg _ (funext fun a =>
      Complex.ext rfl (Complex.pos_iff.1 (hp a)).2.symm))⟩
  have e1 (i) : d i = ‖U i i‖ ^ 2 * grSq M i := by rw [← grSq_tri M hT hd, hD, grSq_diagonal fun a => (hd0 a).ne']
  have e0 : dualGram (diagonal fun a => (d a : ℂ)) = diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ) := by
    rw [dualGram, Matrix.inv_eq_left_inv (B := diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)), diagonal_transpose]
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext a; rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hd0 a).ne']; rfl
  have e2 : dualGram M = Uᵀᴴ * (diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)) * Uᵀ := by
    have hut : IsUnit Uᵀ.det := by rwa [det_transpose]
    rw [← e0, ← hD, dualGram_conj, transpose_nonsing_inv, Matrix.mul_assoc, nonsing_inv_mul_cancel_right _ _ hut,
      ← Matrix.mul_assoc, ← conjTranspose_mul, nonsing_inv_mul _ hut, conjTranspose_one, Matrix.one_mul]
  have e3 : (dualGram M).submatrix Fin.rev Fin.rev = (Uᵀ.submatrix Fin.rev Fin.rev)ᴴ *
      (diagonal fun a : Fin m => (((d a.rev)⁻¹ : ℝ) : ℂ)) * Uᵀ.submatrix Fin.rev Fin.rev := by
    rw [e2, ← submatrix_mul_equiv _ _ _ Fin.revPerm, ← submatrix_mul_equiv _ _ _ Fin.revPerm, conjTranspose_submatrix]
    congr 2
    exact submatrix_diagonal_equiv _ Fin.revPerm
  rw [e3, grSq_tri _ (T := Uᵀ.submatrix Fin.rev Fin.rev) (fun a c hc => hT _ _ (Fin.rev_lt_rev.2 hc)) (fun a => hd _),
    grSq_diagonal (d := fun a => (d a.rev)⁻¹) fun a => inv_ne_zero (hd0 _).ne', e1]
  have := norm_ne_zero_iff.2 (hd i.rev)
  simp only [submatrix_apply, transpose_apply]
  field_simp

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
  {σ σ' : κ.c.F →+* ℂ} {y : CxPts (genStr s.T.Z) σ}

/- English proof (translation)
Use `(x.isMuExp_muExp h).1` as an intermediate fact. Rewrite using `[ToroidalCompactificationData.kap]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem three_le_kap (h : ∃ C, x.IsMuExp C) : 3 ≤ x.kap := by
  have := (x.isMuExp_muExp h).1
  rw [ToroidalCompactificationData.kap]; linarith

/- English proof (translation)
The claim follows from `(tendsto_cutWt (by linarith [three_le_kap x h]) ((Real.exp_pos 1).trans_le (x.exp_le_r σ y))).congr' (by filter_upwards [eventually_ge_atTop 2] with R hR using (x.wt_eq hR hy).symm)`.
-/
theorem tendsto_wt (h : ∃ C, x.IsMuExp C) (hy : ¬ LiesIn y (genBd s.T.Z)) :
    Tendsto (fun R => x.wt σ R y) atTop (𝓝 1) :=
  (tendsto_cutWt (by linarith [three_le_kap x h]) ((Real.exp_pos 1).trans_le (x.exp_le_r σ y))).congr' (by
    filter_upwards [eventually_ge_atTop 2] with R hR using (x.wt_eq hR hy).symm)

/- English proof (translation)
Unfold `ToroidalCompactificationData.wt OddPrimesWithRootsOfUnity.r`. Rewrite using `[liesIn_iff_of_comp (hc z)]`. Simplify using `only [x.nrm_conj σ σ' c hc]`.
-/
theorem wt_conj (c : CxPts (genStr s.T.Z) σ' → CxPts (genStr s.T.Z) σ) (hc : IsConjMap c) (R : ℝ)
    (z : CxPts (genStr s.T.Z) σ') : x.wt σ' R z = x.wt σ R (c z) := by
  unfold ToroidalCompactificationData.wt OddPrimesWithRootsOfUnity.r
  rw [liesIn_iff_of_comp (hc z)]
  simp only [x.nrm_conj σ σ' c hc]

/- English proof (translation)
The claim follows from `EigMet.interp_gram (hs := x.wt_mem R) g (A.cm t)`.
-/
theorem gram_some (R : ℝ) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (t : D.what₂.Tau) :
    (x.eigMetAt σ (some R)).gram y g (DV.tauEmb D t) =
      mix (x.wt σ R y) (x.gram y g _) ((x.hodge σ).gram y g _) :=
  EigMet.interp_gram (hs := x.wt_mem R) g (A.cm t)

/- English proof (translation)
Take `⟨h1, h2⟩` from `h.2 σ y hy g _ v`. Establish `hr : 1 ≤ x.r σ y` using `(Real.one_le_exp zero_le_one).trans (x.exp_le_r σ y)`. Establish `h3 : 1 ≤ x.r σ y ^ C` using `Real.one_le_rpow hr h.1`. Establish `h4 : x.r σ y ^ (-C) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.2 h.1)`. Establish `h5 : 0 ≤ (star v ⬝ᵥ x.gram y g _ *ᵥ v).re` using `(Complex.nonneg_iff.1 ((x.gram_posDef g _).posSemidef.dotProduct_mulVec_nonneg v)).1`.

Take `⟨w0, w1⟩` from `x.wt_mem (σ := σ) (y := y) R`. Rewrite using `[gram_some, mix, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Apply the tactic sequence `constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 w1) (mul_nonneg (sub_nonneg.2 h3) h5), mul_nonneg (sub_nonneg.2 w1) (mul_nonneg (sub_nonneg.2 h4) h5), mul_le_mul_of_nonneg_left h1 w0, mul_le_mul_of_nonneg_left h2 w0]`.
-/
theorem comparison {C : ℝ} (h : x.IsMuExp C) (hy : ¬ LiesIn y (genBd s.T.Z)) (R : ℝ)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (t : D.what₂.Tau) (v : Fin (S.Dw.mult (DV.tauEmb D t)) → ℂ) :
    x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g _ *ᵥ v).re ≤ (star v ⬝ᵥ (x.eigMetAt σ (some R)).gram y g _ *ᵥ v).re ∧
      (star v ⬝ᵥ (x.eigMetAt σ (some R)).gram y g _ *ᵥ v).re ≤ x.r σ y ^ C * (star v ⬝ᵥ x.gram y g _ *ᵥ v).re := by
  obtain ⟨h1, h2⟩ := h.2 σ y hy g _ v
  have hr : 1 ≤ x.r σ y := (Real.one_le_exp zero_le_one).trans (x.exp_le_r σ y)
  have h3 : 1 ≤ x.r σ y ^ C := Real.one_le_rpow hr h.1
  have h4 : x.r σ y ^ (-C) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.2 h.1)
  have h5 : 0 ≤ (star v ⬝ᵥ x.gram y g _ *ᵥ v).re := (Complex.nonneg_iff.1 ((x.gram_posDef g _).posSemidef.dotProduct_mulVec_nonneg v)).1
  obtain ⟨w0, w1⟩ := x.wt_mem (σ := σ) (y := y) R
  rw [gram_some, mix, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, Complex.add_re,
    smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 w1) (mul_nonneg (sub_nonneg.2 h3) h5),
    mul_nonneg (sub_nonneg.2 w1) (mul_nonneg (sub_nonneg.2 h4) h5), mul_le_mul_of_nonneg_left h1 w0,
    mul_le_mul_of_nonneg_left h2 w0]

/- English proof (translation)
Take `⟨w0, w1⟩` from `cutWt_mem_Ioo x.kap hR ((Real.exp_pos 1).trans_le (x.exp_le_r σ y)) hr`. Rewrite `w0`, `w1` using `[← x.wt_eq hR hy]`. Rewrite using `[gram_some, mix]`. Establish `a0 : ((x.wt σ R y : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 w0.ne'`. Establish `a1 : ((1 - x.wt σ R y : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (sub_pos.2 w1).ne'`.

Use `⟨fun e => h (smul_right_injective _ a0 ?_), fun e => h (smul_right_injective _ a1 ?_)⟩` and prove the remaining obligations. Move the coercions through the operations in `at e ⊢`. Rewrite `e` using `[sub_smul, one_smul]`. Take the linear combination `(norm := module) -e`. Move the coercions through the operations in `at e ⊢`.

Take the linear combination `(norm := module) e`.
-/
theorem gram_some_ne {R : ℝ} (hR : 2 ≤ R) (hy : ¬ LiesIn y (genBd s.T.Z)) (hr : x.r σ y ≤ R ^ 2)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (t : D.what₂.Tau)
    (h : x.gram y g (DV.tauEmb D t) ≠ (x.hodge σ).gram y g _) :
    (x.eigMetAt σ (some R)).gram y g (DV.tauEmb D t) ≠ x.gram y g _ ∧
      (x.eigMetAt σ (some R)).gram y g (DV.tauEmb D t) ≠ (x.hodge σ).gram y g _ := by
  obtain ⟨w0, w1⟩ := cutWt_mem_Ioo x.kap hR ((Real.exp_pos 1).trans_le (x.exp_le_r σ y)) hr
  rw [← x.wt_eq hR hy] at w0 w1
  rw [gram_some, mix]
  have a0 : ((x.wt σ R y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 w0.ne'
  have a1 : ((1 - x.wt σ R y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sub_pos.2 w1).ne'
  refine ⟨fun e => h (smul_right_injective _ a0 ?_), fun e => h (smul_right_injective _ a1 ?_)⟩
  · push_cast at e ⊢
    rw [sub_smul, one_smul] at e
    linear_combination (norm := module) -e
  · push_cast at e ⊢
    linear_combination (norm := module) e

/- English proof (translation)
Take `⟨f, hf⟩` from `FinalTheorems.exists_isHodgeFrame_iff.2 hy`. Rewrite using `[x.hodge_gram hf, x'.hodge_gram hf]`.
-/
theorem hodge_indep (x' : ToroidalCompactificationData s) (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z))
    (τ : D.host.E →+* ℂ) : (x.hodge σ).gram y g τ = (x'.hodge σ).gram y g τ := by
  obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy
  rw [x.hodge_gram hf, x'.hodge_gram hf]

/- English proof (translation)
Establish `hp` using `mul_pos Real.two_pi_pos (xiR_pos D)`. Rewrite using `[pn_metsOf_none hg h, Formalism.L2.PjFree.lieFac, ← Real.exp_nat_mul, norm_one, one_pow, one_mul, Fintype.prod_sigma]`. Simplify using `only [← Real.rpow_intCast, Real.rpow_def_of_pos hp, ← Real.exp_sum, ← Finset.mul_sum]`. Use `congr 1`. Use `push_cast`.

Simplify using `only [Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pn_lieFac (Φ : s.Flag) (k : s.Comp) {σ : D.what₂.LL →+* ℂ} {p : Pts (Φ.C k).Y σ} {g : (Φ.C k).FrameAt p}
    (hg : IsHodgeFrame s.U _ g) (a : (D.host.E →+* ℂ) × ℕ → ℕ) {f : (Φ.C k).Y.Fn}
    (h : IsCoord (Φ.C k) p.1 g (fun z => -(a (z.1, z.2) : ℤ)) f 1) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ fun z => -(a (z.1, z.2) : ℤ)) ((cxSt D.what₂.LL).cx _ σ f) p =
      Formalism.L2.PjFree.lieFac S.Dw (xiR D) a ^ 2 := by
  have hp := mul_pos Real.two_pi_pos (xiR_pos D)
  rw [pn_metsOf_none hg h, Formalism.L2.PjFree.lieFac, ← Real.exp_nat_mul, norm_one, one_pow, one_mul, Fintype.prod_sigma]
  simp only [← Real.rpow_intCast, Real.rpow_def_of_pos hp, ← Real.exp_sum, ← Finset.mul_sum]
  congr 1
  push_cast
  simp only [Finset.sum_neg_distrib]
  ring

end GlobalTheory.ShFam.MetsTest
