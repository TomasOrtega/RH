import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords

open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem I_pow_three' : I ^ 3 = -I := by
  rw [pow_succ, I_sq, neg_one_mul]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem eq_sum_coord_smul_basis (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
private theorem clm_apply_eq_sum_wd_wdb_basis (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [eq_sum_coord_smul_basis w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [← Complex.re_add_im (w b), add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
    map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((w b).im * D (I • bas n b)) * Complex.I_sq

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem fderiv_comp_holomorphic_apply {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by
  have hG' : HasFDerivAt G ((fderiv ℂ G y).restrictScalars ℝ) y := hG.hasFDerivAt.restrictScalars ℝ
  rw [(hU.hasFDerivAt.comp y hG').fderiv]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wdb_comp_holomorphic_eq_sum_conj {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  unfold wdb
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wd_comp_holomorphic_eq_sum {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wd n k (U ∘ G) y = ∑ b, wd n b U (G y) * fderiv ℂ G y (bas n k) b := by
  unfold wd
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem differentiableAt_fderiv_basis_coord_of_contDiffAt {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ G) y := hG.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℂ 1 (fun v => fderiv ℂ G v (bas n k)) y := h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℂ 1 (fun v => (EuclideanSpace.proj b : V n →L[ℂ] ℂ) (fderiv ℂ G v (bas n k))) y :=
    (EuclideanSpace.proj b : V n →L[ℂ] ℂ).contDiff.contDiffAt.comp y h2
  exact h3.differentiableAt one_ne_zero

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem differentiableAt_wdb_of_contDiffAt {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (I • bas n k)).const_mul I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem wd_finset_sum {ι : Type*} (s : Finset ι) (Φ : ι → V n → ℂ) (y : V n)
    (hΦ : ∀ i ∈ s, DifferentiableAt ℝ (Φ i) y) (j : Fin n) :
    wd n j (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, wd n j (Φ i) y := by
  have hF : fderiv ℝ (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, fderiv ℝ (Φ i) y := by
    have H := HasFDerivAt.sum (u := s) (A := Φ) fun i hi => (hΦ i hi).hasFDerivAt
    try simp only [Finset.sum_fn] at H
    exact H.fderiv
  simp only [wd, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wd_mul_eq_leibniz {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. A detailed English derivation is pending.
-/
private theorem wd_conj_holomorphic_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cmpa_hess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) (j k : Fin n) :
    wd n j (wdb n k (h ∘ τ)) x = ∑ m, ∑ l, wd n l (wdb n m h) (τ x) *
      (fderiv ℂ τ x (bas n j)) l * conj ((fderiv ℂ τ x (bas n k)) m) := by
  have hτc : ContDiffOn ℂ ∞ τ U := by
    rw [contDiffOn_piLp]
    intro i
    exact contDiffOn_of_differentiableOn n _ U hU
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hτ)
  have hG : ContDiffAt ℂ 2 τ x := (contDiffOn_infty.1 hτc 2).contDiffAt (hU.mem_nhds hxU)
  have hGd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℂ τ v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℝ h (τ v) := by
    have h1 : ∀ᶠ w in 𝓝 (τ x), DifferentiableAt ℝ h w :=
      (hh.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
    exact Filter.Tendsto.eventually hG.continuousAt h1
  have ev : wdb n k (h ∘ τ) =ᶠ[𝓝 x]
      fun v => ∑ b, wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b) := by
    filter_upwards [hGd, hUd] with v h1 h2
    exact wdb_comp_holomorphic_eq_sum_conj h2 h1 k
  have hGy : DifferentiableAt ℂ τ x := hG.differentiableAt (by simp)
  have e1 : wd n j (wdb n k (h ∘ τ)) x = wd n j (fun v => ∑ b, wdb n b h (τ v) *
      conj (fderiv ℂ τ v (bas n k) b)) x := by
    simp only [wd, ev.fderiv_eq]
  have hp : ∀ b, DifferentiableAt ℝ (fun v => wdb n b h (τ v)) x := fun b =>
    (differentiableAt_wdb_of_contDiffAt hh b).comp x (hGy.restrictScalars ℝ)
  have hq : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ τ v (bas n k) b)) x :=
    fun b => ((differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b).restrictScalars ℝ).star
  rw [e1, wd_finset_sum Finset.univ (fun b v => wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b))
      x (fun b _ => (hp b).mul (hq b)) j]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wd_mul_eq_leibniz (hp b) (hq b) j, wd_conj_holomorphic_eq_zero (differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b) j, mul_zero, add_zero]
  have e2 := wd_comp_holomorphic_eq_sum (U := wdb n b h) (differentiableAt_wdb_of_contDiffAt hh b) hGy j
  simp only [Function.comp_def] at e2
  rw [e2, Finset.sum_mul]

end

end ReciprocityTheory.L2DbarEstimates.Y
