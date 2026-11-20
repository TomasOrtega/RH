import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOneStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open Matrix Filter Formalism.MainNotions.S Formalism.REAL
open scoped InnerProductSpace ComplexOrder ContDiff Topology Matrix.Norms.L2Operator MatrixOrder

noncomputable section

namespace GlobalTheory.Dec.PsiAn

variable {n : ℕ}

/- English proof (translation)
Establish `e' : p * h = -(h * p)` using `eq_neg_of_add_eq_zero_left e`. Establish `hcol : ∀ j, h *ᵥ ⇑(hp.1.eigenvectorBasis j) = 0`. Introduce `j`. Use `set v := ⇑(hp.1.eigenvectorBasis j) with hvdef`. Use `set c : ℂ := ((hp.1.eigenvalues j : ℝ) : ℂ) with hcdef`.

Establish `hv : p *ᵥ v = c • v`. Rewrite using `[hvdef, hp.1.mulVec_eigenvectorBasis j, RCLike.real_smul_eq_coe_smul (K := ℂ)]`. Both sides reduce to the same expression. Establish `hc : 0 < c` using `Complex.zero_lt_real.2 (hp.eigenvalues_pos j)`. Assume the negation of the conclusion as `hw`.

Establish `hpos` using `hp.dotProduct_mulVec_pos hw`. Establish `hpw : p *ᵥ (h *ᵥ v) = -(c • (h *ᵥ v))`. Rewrite using `[mulVec_mulVec, e', neg_mulVec, ← mulVec_mulVec, hv, mulVec_smul]`. Rewrite `hpos` using `[hpw, dotProduct_neg, dotProduct_smul, smul_eq_mul]`. Establish `hs` using `dotProduct_star_self_nonneg (h *ᵥ v)`.

Establish `hnn : 0 ≤ c * (star (h *ᵥ v) ⬝ᵥ (h *ᵥ v))` using `mul_nonneg hc.le hs`. Conclude with `lt_irrefl _ (hpos.trans_le (neg_nonpos.2 hnn))`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hp.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Establish `hU : h * U = 0`. Use extensionality with `i j`.

Establish `hij` using `congrFun (hcol j) i`. Simplify `hij` using `[hUdef, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hUU : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.1 hp.1.eigenvectorUnitary.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_anticomm {p h : Matrix (Fin n) (Fin n) ℂ} (hp : p.PosDef) (e : p * h + h * p = 0) :
    h = 0 := by
  have e' : p * h = -(h * p) := eq_neg_of_add_eq_zero_left e
  have hcol : ∀ j, h *ᵥ ⇑(hp.1.eigenvectorBasis j) = 0 := by
    intro j
    set v := ⇑(hp.1.eigenvectorBasis j) with hvdef
    set c : ℂ := ((hp.1.eigenvalues j : ℝ) : ℂ) with hcdef
    have hv : p *ᵥ v = c • v := by
      rw [hvdef, hp.1.mulVec_eigenvectorBasis j, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    have hc : 0 < c := Complex.zero_lt_real.2 (hp.eigenvalues_pos j)
    by_contra hw
    have hpos := hp.dotProduct_mulVec_pos hw
    have hpw : p *ᵥ (h *ᵥ v) = -(c • (h *ᵥ v)) := by
      rw [mulVec_mulVec, e', neg_mulVec, ← mulVec_mulVec, hv, mulVec_smul]
    rw [hpw, dotProduct_neg, dotProduct_smul, smul_eq_mul] at hpos
    have hs := dotProduct_star_self_nonneg (h *ᵥ v)
    have hnn : 0 ≤ c * (star (h *ᵥ v) ⬝ᵥ (h *ᵥ v)) := mul_nonneg hc.le hs
    exact lt_irrefl _ (hpos.trans_le (neg_nonpos.2 hnn))
  set U : Matrix (Fin n) (Fin n) ℂ := (hp.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : h * U = 0 := by
    ext i j
    have hij := congrFun (hcol j) i
    simpa [hUdef, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hij
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hp.1.eigenvectorUnitary.2
  calc h = h * (U * star U) := by rw [hUU, mul_one]
    _ = 0 := by rw [← mul_assoc, hU, zero_mul]

/- English proof (translation)
Establish `h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ gᴴ * g` using `Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_conjTranspose_mul_self g)`. Establish `hsq : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g` using `CFC.sqrt_mul_sqrt_self _ h0`. Establish `hgH : IsUnit gᴴ` using `by rw [← Matrix.star_eq_conjTranspose]; exact hg.star`. Establish `hu : IsUnit (gᴴ * g)` using `hgH.mul hg`. Establish `hsu : IsUnit (CFC.sqrt (gᴴ * g))` using `(CFC.isUnit_sqrt_iff _ h0).2 hu`.

Establish `hpd : (CFC.sqrt (gᴴ * g)).PosDef` using `(Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).posDef_iff_isUnit.2 hsu`. Conclude with `posPart_eq_of_sq hpd hsq`.
-/
theorem posPart_eq_sqrt {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) : posPart g = CFC.sqrt (gᴴ * g) := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ gᴴ * g :=
    Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_conjTranspose_mul_self g)
  have hsq : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ h0
  have hgH : IsUnit gᴴ := by rw [← Matrix.star_eq_conjTranspose]; exact hg.star
  have hu : IsUnit (gᴴ * g) := hgH.mul hg
  have hsu : IsUnit (CFC.sqrt (gᴴ * g)) := (CFC.isUnit_sqrt_iff _ h0).2 hu
  have hpd : (CFC.sqrt (gᴴ * g)).PosDef :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).posDef_iff_isUnit.2 hsu
  exact posPart_eq_of_sq hpd hsq

/- English proof (translation)
Establish `hev : (fun x : Matrix (Fin n) (Fin n) ℂ => CFC.sqrt (star x * x)) =ᶠ[𝓝 g] posPart` using `by filter_upwards [Units.isOpen.mem_nhds hg] with x hx`. Rewrite using `[Matrix.star_eq_conjTranspose]`. Conclude with `(posPart_eq_sqrt hx).symm`. Use `ContinuousAt.congr ?_ hev` and prove the remaining obligations. Establish `hc : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => star x * x)` using `continuous_star.mul continuous_id`.

Establish `h0 : ∀ x : Matrix (Fin n) (Fin n) ℂ, star x * x ∈ {a : Matrix (Fin n) (Fin n) ℂ | 0 ≤ a}` using `fun x => by show 0 ≤ star x * x`. Rewrite using `[Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_conjTranspose_mul_self x)`. Conclude with `(CFC.continuousOn_sqrt.comp_continuous hc h0).continuousAt`.
-/
theorem continuousAt_posPart {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) : ContinuousAt posPart g := by
  have hev : (fun x : Matrix (Fin n) (Fin n) ℂ => CFC.sqrt (star x * x)) =ᶠ[𝓝 g] posPart := by
    filter_upwards [Units.isOpen.mem_nhds hg] with x hx
    rw [Matrix.star_eq_conjTranspose]
    exact (posPart_eq_sqrt hx).symm
  refine ContinuousAt.congr ?_ hev
  have hc : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => star x * x) :=
    continuous_star.mul continuous_id
  have h0 : ∀ x : Matrix (Fin n) (Fin n) ℂ, star x * x ∈ {a : Matrix (Fin n) (Fin n) ℂ | 0 ≤ a} :=
    fun x => by
      show 0 ≤ star x * x
      rw [Matrix.star_eq_conjTranspose]
      exact Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_conjTranspose_mul_self x)
  exact (CFC.continuousOn_sqrt.comp_continuous hc h0).continuousAt

/- English proof (translation)
Take `⟨hpd, hsq⟩` from `posPart_posDef_sq hg`. Use `set p0 := posPart g with hp0`. Set `T : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ` to `p0 • ContinuousLinearMap.id ℂ _ + (ContinuousLinearMap.id ℂ _).smulRight p0`. Establish `hT : ∀ x, T x = p0 * x + x * p0` using `fun x => rfl`. Establish `hTinj : Function.Injective T`.

Introduce `x y hxy`. Rewrite `hxy` using `[hT, hT]`. Establish `hz : p0 * (x - y) + (x - y) * p0 = 0`. Rewrite using `[mul_sub, sub_mul, show p0 * x - p0 * y + (x * p0 - y * p0) = (p0 * x + x * p0) - (p0 * y + y * p0) by abel, hxy, sub_self]`. Conclude with `sub_eq_zero.1 (eq_zero_of_anticomm hpd hz)`.

Set `f' : Matrix (Fin n) (Fin n) ℂ ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ` to `(LinearEquiv.ofInjectiveEndo (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) hTinj).toContinuousLinearEquiv`. Establish `hf' : HasFDerivAt (fun p : Matrix (Fin n) (Fin n) ℂ => p * p) (f' : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) p0`. Use `((hasFDerivAt_id (𝕜 := ℂ) p0).mul' (hasFDerivAt_id (𝕜 := ℂ) p0)).congr_fderiv ?_` and prove the remaining obligations. Use `ContinuousLinearMap.ext fun x => ?_` and prove the remaining obligations. Use `show p0 * x + x * p0 = T x`.

Rewrite using `[hT]`. Establish `hF : ContDiffAt ℂ ω (fun p : Matrix (Fin n) (Fin n) ℂ => p * p) p0` using `contDiffAt_id.mul contDiffAt_id`. Establish `hn : (ω : WithTop ℕ∞) ≠ 0` using `by simp`. Establish `hL : AnalyticAt ℂ (hF.localInverse hf' hn) (p0 * p0)` using `(hF.to_localInverse hf' hn).analyticAt`. Establish `hleft : ∀ᶠ p in 𝓝 p0, hF.localInverse hf' hn (p * p) = p` using `(hF.hasStrictFDerivAt' hf' hn).eventually_left_inverse`.

Establish `hev : posPart =ᶠ[𝓝 g] fun x => hF.localInverse hf' hn (xᴴ * x)` using `by filter_upwards [(continuousAt_posPart hg).eventually hleft, Units.isOpen.mem_nhds hg] with x hx hux`. Rewrite using `[← (posPart_posDef_sq hux).2]`. Conclude with `hx.symm`. Establish `hstar : AnalyticAt ℝ (fun x : Matrix (Fin n) (Fin n) ℂ => star x) g` using `((starL' ℝ : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).analyticAt g`. Establish `hq : AnalyticAt ℝ (fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ * x) g`.

Establish `h3` using `hstar.mul (analyticAt_id : AnalyticAt ℝ id g)`. Establish `e3 : ((fun x : Matrix (Fin n) (Fin n) ℂ => star x) * id) = fun x => xᴴ * x`. Use function extensionality and compare the values at `x`. Simplify using `[Matrix.star_eq_conjTranspose]`. Rewrite `h3` using `[e3]`.

Conclude with `h3`. Establish `hL' : AnalyticAt ℝ (hF.localInverse hf' hn) (gᴴ * g)`. Rewrite using `[← hsq]`. Conclude with `hL.restrictScalars`. Conclude with `(AnalyticAt.comp (f := fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ * x) hL' hq).congr hev.symm`.
-/
theorem analyticAt_posPart {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) : AnalyticAt ℝ posPart g := by
  obtain ⟨hpd, hsq⟩ := posPart_posDef_sq hg
  set p0 := posPart g with hp0
  let T : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    p0 • ContinuousLinearMap.id ℂ _ + (ContinuousLinearMap.id ℂ _).smulRight p0
  have hT : ∀ x, T x = p0 * x + x * p0 := fun x => rfl
  have hTinj : Function.Injective T := by
    intro x y hxy
    rw [hT, hT] at hxy
    have hz : p0 * (x - y) + (x - y) * p0 = 0 := by
      rw [mul_sub, sub_mul,
        show p0 * x - p0 * y + (x * p0 - y * p0) = (p0 * x + x * p0) - (p0 * y + y * p0) by abel,
        hxy, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_anticomm hpd hz)
  let f' : Matrix (Fin n) (Fin n) ℂ ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (LinearEquiv.ofInjectiveEndo (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
      hTinj).toContinuousLinearEquiv
  have hf' : HasFDerivAt (fun p : Matrix (Fin n) (Fin n) ℂ => p * p)
      (f' : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) p0 := by
    refine ((hasFDerivAt_id (𝕜 := ℂ) p0).mul' (hasFDerivAt_id (𝕜 := ℂ) p0)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun x => ?_
    show p0 * x + x * p0 = T x
    rw [hT]
  have hF : ContDiffAt ℂ ω (fun p : Matrix (Fin n) (Fin n) ℂ => p * p) p0 :=
    contDiffAt_id.mul contDiffAt_id
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hL : AnalyticAt ℂ (hF.localInverse hf' hn) (p0 * p0) :=
    (hF.to_localInverse hf' hn).analyticAt
  have hleft : ∀ᶠ p in 𝓝 p0, hF.localInverse hf' hn (p * p) = p :=
    (hF.hasStrictFDerivAt' hf' hn).eventually_left_inverse
  have hev : posPart =ᶠ[𝓝 g] fun x => hF.localInverse hf' hn (xᴴ * x) := by
    filter_upwards [(continuousAt_posPart hg).eventually hleft, Units.isOpen.mem_nhds hg]
      with x hx hux
    rw [← (posPart_posDef_sq hux).2]
    exact hx.symm
  have hstar : AnalyticAt ℝ (fun x : Matrix (Fin n) (Fin n) ℂ => star x) g :=
    ((starL' ℝ : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).analyticAt g
  have hq : AnalyticAt ℝ (fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ * x) g := by
    have h3 := hstar.mul (analyticAt_id : AnalyticAt ℝ id g)
    have e3 : ((fun x : Matrix (Fin n) (Fin n) ℂ => star x) * id) = fun x => xᴴ * x := by
      funext x
      simp [Matrix.star_eq_conjTranspose]
    rw [e3] at h3
    exact h3
  have hL' : AnalyticAt ℝ (hF.localInverse hf' hn) (gᴴ * g) := by
    rw [← hsq]; exact hL.restrictScalars
  exact (AnalyticAt.comp (f := fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ * x) hL' hq).congr hev.symm

/- English proof (translation)
Establish `hu : IsUnit (posPart g)` using `(posPart_posDef_sq hg).1.isUnit`. Establish `hinv : AnalyticAt ℝ (fun z : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (posPart z)) g` using `AnalyticAt.comp (g := Ring.inverse) (f := posPart) (analyticAt_inverse (𝕜 := ℝ) hu.unit) (analyticAt_posPart hg)`. Establish `h2` using `(analyticAt_id : AnalyticAt ℝ id g).mul hinv`. Establish `e2 : (id * fun z : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (posPart z)) = fun z => z * (posPart z)⁻¹`. Use function extensionality and compare the values at `z`.

Simplify using `[Matrix.nonsing_inv_eq_ringInverse]`. Rewrite `h2` using `[e2]`. Conclude with `h2`.
-/
theorem analyticAt_unitPart {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) :
    AnalyticAt ℝ (fun z : Matrix (Fin n) (Fin n) ℂ => z * (posPart z)⁻¹) g := by
  have hu : IsUnit (posPart g) := (posPart_posDef_sq hg).1.isUnit
  have hinv : AnalyticAt ℝ (fun z : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (posPart z)) g :=
    AnalyticAt.comp (g := Ring.inverse) (f := posPart) (analyticAt_inverse (𝕜 := ℝ) hu.unit) (analyticAt_posPart hg)
  have h2 := (analyticAt_id : AnalyticAt ℝ id g).mul hinv
  have e2 : (id * fun z : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (posPart z)) =
      fun z => z * (posPart z)⁻¹ := by
    funext z
    simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [e2] at h2
  exact h2

/- English proof (translation)
Establish `hJ : gᴴ * Jm ε * g = Jm ε` using `hg`. Take `⟨hgJg, hgu⟩` from `indefinite_unitary_preserves_form hJ`. Take `⟨hpd, hsq⟩` from `posPart_posDef_sq hgu`. Use `set p := posPart g with hpdef`. Use `set J := Jm ε with hJdef`.

Establish `hJJ : J * J = 1` using `Jm_mul_self ε`. Establish `hJH : Jᴴ = J` using `Jm_conjTranspose ε`. Establish `hpH : pᴴ = p` using `hpd.1`. Establish `hpdet : IsUnit p.det` using `(Matrix.isUnit_iff_isUnit_det p).1 hpd.isUnit`. Establish `hpp : p * p⁻¹ = 1` using `Matrix.mul_nonsing_inv p hpdet`.

Establish `hpp' : p⁻¹ * p = 1` using `Matrix.nonsing_inv_mul p hpdet`. Establish `hpinvH : (p⁻¹)ᴴ = p⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hpH]`. Establish `hJu : IsUnit J` using `⟨⟨J, J, hJJ, hJJ⟩, rfl⟩`. Establish `hrpd : (J * p * J).PosDef`. Establish `h1` using `hpd.conjTranspose_mul_mul_same (B := J) (Matrix.mulVec_injective_iff_isUnit.2 hJu)`.

Rewrite `h1` using `[hJH]`. Then use the resulting hypothesis. Establish `hinv : (gᴴ * g)⁻¹ = J * gᴴ * g * J`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hr : J * p * J = p⁻¹`.

Establish `e1 : (J * p * J) * (J * p * J) = (p⁻¹)ᴴ * p⁻¹`. Rewrite using `[hpinvH, ← Matrix.mul_inv_rev, hsq, hinv]`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : p⁻¹ * p⁻¹ = (p⁻¹)ᴴ * p⁻¹` using `by rw [hpinvH]`. Conclude with `(posPart_eq_of_sq hrpd e1).symm.trans (posPart_eq_of_sq hpd.inv e2)`.

Establish `hpJ : p⁻¹ * J = J * p` using `by rw [← hr, mul_assoc, hJJ, mul_one]`. Establish `hkk : (g * p⁻¹)ᴴ * (g * p⁻¹) = 1`. Rewrite using `[Matrix.conjTranspose_mul, hpinvH]`. Combine the equalities or inequalities in the displayed calculation. Establish `hkJk : (g * p⁻¹)ᴴ * J * (g * p⁻¹) = J`.

Rewrite using `[Matrix.conjTranspose_mul, hpinvH]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmem : g * p⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ` using `Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact hkk)`. Establish `hkk' : (g * p⁻¹) * (g * p⁻¹)ᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`.

Conclude with `Matrix.mem_unitaryGroup_iff.1 hmem`. Use `show g * p⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * p⁻¹ * J = J * (g * p⁻¹)`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unitPart_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g * (posPart g)⁻¹ ∈ Kset ε := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  obtain ⟨hgJg, hgu⟩ := indefinite_unitary_preserves_form hJ
  obtain ⟨hpd, hsq⟩ := posPart_posDef_sq hgu
  set p := posPart g with hpdef
  set J := Jm ε with hJdef
  have hJJ : J * J = 1 := Jm_mul_self ε
  have hJH : Jᴴ = J := Jm_conjTranspose ε
  have hpH : pᴴ = p := hpd.1
  have hpdet : IsUnit p.det := (Matrix.isUnit_iff_isUnit_det p).1 hpd.isUnit
  have hpp : p * p⁻¹ = 1 := Matrix.mul_nonsing_inv p hpdet
  have hpp' : p⁻¹ * p = 1 := Matrix.nonsing_inv_mul p hpdet
  have hpinvH : (p⁻¹)ᴴ = p⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hpH]
  have hJu : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  have hrpd : (J * p * J).PosDef := by
    have h1 := hpd.conjTranspose_mul_mul_same (B := J) (Matrix.mulVec_injective_iff_isUnit.2 hJu)
    rwa [hJH] at h1
  have hinv : (gᴴ * g)⁻¹ = J * gᴴ * g * J := by
    apply Matrix.inv_eq_left_inv
    calc J * gᴴ * g * J * (gᴴ * g) = J * gᴴ * (g * J * gᴴ) * g := by simp only [mul_assoc]
      _ = J * (gᴴ * J * g) := by rw [hgJg]; simp only [mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have hr : J * p * J = p⁻¹ := by
    have e1 : (J * p * J) * (J * p * J) = (p⁻¹)ᴴ * p⁻¹ := by
      rw [hpinvH, ← Matrix.mul_inv_rev, hsq, hinv]
      calc J * p * J * (J * p * J) = J * p * (J * J) * p * J := by simp only [mul_assoc]
        _ = J * (p * p) * J := by rw [hJJ]; simp only [mul_assoc, mul_one]
        _ = J * gᴴ * g * J := by rw [hsq]; simp only [mul_assoc]
    have e2 : p⁻¹ * p⁻¹ = (p⁻¹)ᴴ * p⁻¹ := by rw [hpinvH]
    exact (posPart_eq_of_sq hrpd e1).symm.trans (posPart_eq_of_sq hpd.inv e2)
  have hpJ : p⁻¹ * J = J * p := by rw [← hr, mul_assoc, hJJ, mul_one]
  have hkk : (g * p⁻¹)ᴴ * (g * p⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, hpinvH]
    calc p⁻¹ * gᴴ * (g * p⁻¹) = p⁻¹ * (gᴴ * g) * p⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [← hsq]; simp only [mul_assoc]; rw [hpp, mul_one, hpp']
  have hkJk : (g * p⁻¹)ᴴ * J * (g * p⁻¹) = J := by
    rw [Matrix.conjTranspose_mul, hpinvH]
    calc p⁻¹ * gᴴ * J * (g * p⁻¹) = p⁻¹ * (gᴴ * J * g) * p⁻¹ := by simp only [mul_assoc]
      _ = J * (p * p⁻¹) := by rw [hJ, hpJ, mul_assoc]
      _ = J := by rw [hpp, mul_one]
  have hmem : g * p⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact hkk)
  have hkk' : (g * p⁻¹) * (g * p⁻¹)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hmem
  show g * p⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * p⁻¹ * J = J * (g * p⁻¹)
  refine ⟨hmem, ?_⟩
  calc g * p⁻¹ * J = g * p⁻¹ * ((g * p⁻¹)ᴴ * J * (g * p⁻¹)) := by rw [hkJk]
    _ = (g * p⁻¹ * (g * p⁻¹)ᴴ) * J * (g * p⁻¹) := by simp only [mul_assoc]
    _ = J * (g * p⁻¹) := by rw [hkk', one_mul]

def projJ (ε : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (y + Jm ε * y * Jm ε)

/- English proof (translation)
Establish `hJJ : Jm ε * Jm ε = 1` using `Jm_mul_self ε`. Establish `hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← mul_assoc, hJJ, one_mul]`. Simplify using `only [projJ, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, hJJ, hJJ', mul_one]`. Rewrite using `[add_comm]`.
-/
theorem projJ_comm (ε : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) :
    projJ ε y * Jm ε = Jm ε * projJ ε y := by
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← mul_assoc, hJJ, one_mul]
  simp only [projJ, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, hJJ, hJJ', mul_one]
  rw [add_comm]

/- English proof (translation)
Establish `hy : Jm ε * y * Jm ε = y` using `by rw [← h, mul_assoc, Jm_mul_self, mul_one]`. Rewrite using `[projJ, hy, ← two_smul ℂ y, smul_smul]`. Evaluate the numerical expressions.
-/
theorem projJ_of_comm {ε : Fin n → Bool} {y : Matrix (Fin n) (Fin n) ℂ} (h : y * Jm ε = Jm ε * y) :
    projJ ε y = y := by
  have hy : Jm ε * y * Jm ε = y := by rw [← h, mul_assoc, Jm_mul_self, mul_one]
  rw [projJ, hy, ← two_smul ℂ y, smul_smul]
  norm_num

/- English proof (translation)
Use `show Differentiable ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => (1 / 2 : ℂ) • (y + Jm ε * y * Jm ε))`. Use `fun_prop`.
-/
theorem differentiable_projJ (ε : Fin n → Bool) : Differentiable ℂ (projJ ε) := by
  show Differentiable ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => (1 / 2 : ℂ) • (y + Jm ε * y * Jm ε))
  fun_prop

def ofL (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv

/- English proof (translation)
Use `set s : Set (Matrix (Fin n) (Fin n) ℂ) := {y | IsUnit (projJ ε y)} with hsdef`. Establish `hs : IsOpen s` using `Units.isOpen.preimage (differentiable_projJ ε).continuous`. Establish `hks : k ∈ s` using `by show IsUnit (projJ ε k)`. Rewrite using `[projJ_of_comm hk.2]`. Conclude with `hk.1`.

Use `GlobalTheory.SCV.analyticAt_of_differentiableOn (s := s) ?_ (hs.mem_nhds hks)` and prove the remaining obligations. Introduce `y hy`. Establish `hmaps : Set.MapsTo (fun x => (ofL n).symm (projJ ε x)) s {y | Matrix.of y ∈ KC ε}` using `fun x hx => (show IsUnit (projJ ε x) ∧ projJ ε x * Jm ε = Jm ε * projJ ε x from ⟨hx, projJ_comm ε x⟩)`. Establish `h1 : DifferentiableWithinAt ℂ (fun x => (ofL n).symm (projJ ε x)) s y` using `(((ofL n).symm.differentiable.comp (differentiable_projJ ε)) y).differentiableWithinAt`. Conclude with `(hf _ (hmaps hy)).comp y h1 hmaps`.
-/
theorem analyticAt_comp_projJ {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => f (Matrix.of y)) {y | Matrix.of y ∈ KC ε})
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KC ε) : AnalyticAt ℂ (fun y => f (projJ ε y)) k := by
  set s : Set (Matrix (Fin n) (Fin n) ℂ) := {y | IsUnit (projJ ε y)} with hsdef
  have hs : IsOpen s := Units.isOpen.preimage (differentiable_projJ ε).continuous
  have hks : k ∈ s := by
    show IsUnit (projJ ε k)
    rw [projJ_of_comm hk.2]
    exact hk.1
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := s) ?_ (hs.mem_nhds hks)
  intro y hy
  have hmaps : Set.MapsTo (fun x => (ofL n).symm (projJ ε x)) s {y | Matrix.of y ∈ KC ε} :=
    fun x hx => (show IsUnit (projJ ε x) ∧ projJ ε x * Jm ε = Jm ε * projJ ε x from ⟨hx, projJ_comm ε x⟩)
  have h1 : DifferentiableWithinAt ℂ (fun x => (ofL n).symm (projJ ε x)) s y :=
    (((ofL n).symm.differentiable.comp (differentiable_projJ ε)) y).differentiableWithinAt
  exact (hf _ (hmaps hy)).comp y h1 hmaps

end GlobalTheory.Dec.PsiAn

namespace GlobalTheory.Dec

open PsiAn

/- English proof (translation)
Unfold `PsiAnalytic`. Introduce `n ε lam W _ _ τ w hlam htau u v g hg`. Take `⟨hUo, hPD, hpsd, -⟩` from `hB n ε lam W τ w hlam htau`. Establish `: FiniteDimensional ℂ W` using `htau.1`. Establish `hJ : Formalism.REAL.inUJ ε g` using `hg`.

Establish `hgu : IsUnit g` using `(indefinite_unitary_preserves_form hJ).2`. Establish `hpd` using `(posPart_posDef_sq hgu).1`. Use `set b := stdOrthonormalBasis ℂ W with hbdef`. Use `⟨fun z => ∑ i, ⟪u, τ (projJ ε (Matrix.of z * (posPart (Matrix.of z))⁻¹)) (b i)⟫_ℂ * ⟪b i, ps ε lam τ w (posPart (Matrix.of z)) v⟫_ℂ, ?_, ?_⟩` and prove the remaining obligations. Establish `hofz : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ => Matrix.of z) (fun i j => g i j)` using `(((ofL n : (Fin n → Fin n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ).restrictScalars ℝ)).analyticAt _`.

Establish `hk : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ => Matrix.of z * (posPart (Matrix.of z))⁻¹) (fun i j => g i j)` using `AnalyticAt.comp (g := fun M : Matrix (Fin n) (Fin n) ℂ => M * (posPart M)⁻¹) (f := fun z : Fin n → Fin n → ℂ => Matrix.of z) (analyticAt_unitPart hgu) hofz`. Establish `hp : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ => (ofL n).symm (posPart (Matrix.of z))) (fun i j => g i j)` using `AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => posPart (Matrix.of z)) ((((ofL n).symm : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → Fin n → ℂ)).restrictScalars ℝ).analyticAt _) (AnalyticAt.comp (g := posPart) (f := fun z : Fin n → Fin n → ℂ => Matrix.of z) (analyticAt_posPart hgu …`. Establish `hkK` using `unitPart_mem hg`. Establish `hkKC : g * (posPart g)⁻¹ ∈ KC ε` using `by show IsUnit (g * (posPart g)⁻¹) ∧ g * (posPart g)⁻¹ * Jm ε = Jm ε * (g * (posPart g)⁻¹)`. Use `⟨⟨⟨g * (posPart g)⁻¹, star (g * (posPart g)⁻¹), Matrix.mem_unitaryGroup_iff.1 hkK.1, Matrix.mem_unitaryGroup_iff'.1 hkK.1⟩, rfl⟩, hkK.2⟩` and prove the remaining obligations.

Establish `hp0U : (ofL n).symm (posPart g) ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}` using `hPD _ hpd`. Use `Finset.analyticAt_fun_sum _ (fun i _ => ?_)` and prove the remaining obligations. Establish `hA : AnalyticAt ℂ (fun y => ⟪u, τ (projJ ε y) (b i)⟫_ℂ) (g * (posPart g)⁻¹)` using `analyticAt_comp_projJ (f := fun M => ⟪u, τ M (b i)⟫_ℂ) (htau.2.2.1 u (b i)) hkKC`. Establish `hBd : DifferentiableOn ℂ (fun x : Fin n → Fin n → ℂ => ⟪b i, ps ε lam τ w (Matrix.of x) v⟫_ℂ) {z | Matrix.of z ∈ U1 ε}` using `(innerSL ℂ (b i)).differentiable.comp_differentiableOn (hpsd.clm_apply (differentiableOn_const v))`. Establish `hBa : AnalyticAt ℂ (fun x : Fin n → Fin n → ℂ => ⟪b i, ps ε lam τ w (Matrix.of x) v⟫_ℂ) ((ofL n).symm (posPart g))` using `GlobalTheory.SCV.analyticAt_of_differentiableOn hBd (hUo.mem_nhds hp0U)`.

Conclude with `(AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => Matrix.of z * (posPart (Matrix.of z))⁻¹) hA.restrictScalars hk).mul (AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => (ofL n).symm (posPart (Matrix.of z))) hBa.restrictScalars hp)`. Use `Filter.Eventually.of_forall (fun z hz => ?_)` and prove the remaining obligations. Establish `hc` using `(unitPart_mem hz).2`. Simplify using `only [Psi, ContinuousLinearMap.comp_apply]`. Use `conv_lhs => rw [← b.sum_repr' (ps ε lam τ w (posPart (Matrix.of z)) v)]`.

Rewrite using `[map_sum, inner_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_right, projJ_of_comm hc]`. Conclude with `mul_comm _ _`.
-/
theorem psiAnalytic_of_psBasic (hB : PsBasic) : PsiAnalytic := by
  unfold PsiAnalytic
  intro n ε lam W _ _ τ w hlam htau u v g hg
  obtain ⟨hUo, hPD, hpsd, -⟩ := hB n ε lam W τ w hlam htau
  have : FiniteDimensional ℂ W := htau.1
  have hJ : Formalism.REAL.inUJ ε g := hg
  have hgu : IsUnit g := (indefinite_unitary_preserves_form hJ).2
  have hpd := (posPart_posDef_sq hgu).1
  set b := stdOrthonormalBasis ℂ W with hbdef
  refine ⟨fun z => ∑ i, ⟪u, τ (projJ ε (Matrix.of z * (posPart (Matrix.of z))⁻¹)) (b i)⟫_ℂ *
      ⟪b i, ps ε lam τ w (posPart (Matrix.of z)) v⟫_ℂ, ?_, ?_⟩
  · have hofz : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ => Matrix.of z) (fun i j => g i j) :=
      (((ofL n : (Fin n → Fin n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ).restrictScalars ℝ)).analyticAt _
    have hk : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ =>
        Matrix.of z * (posPart (Matrix.of z))⁻¹) (fun i j => g i j) :=
      AnalyticAt.comp (g := fun M : Matrix (Fin n) (Fin n) ℂ => M * (posPart M)⁻¹)
        (f := fun z : Fin n → Fin n → ℂ => Matrix.of z) (analyticAt_unitPart hgu) hofz
    have hp : AnalyticAt ℝ (fun z : Fin n → Fin n → ℂ => (ofL n).symm (posPart (Matrix.of z)))
        (fun i j => g i j) :=
      AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => posPart (Matrix.of z))
        ((((ofL n).symm : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → Fin n → ℂ)).restrictScalars ℝ).analyticAt _)
        (AnalyticAt.comp (g := posPart) (f := fun z : Fin n → Fin n → ℂ => Matrix.of z)
          (analyticAt_posPart hgu) hofz)
    have hkK := unitPart_mem hg
    have hkKC : g * (posPart g)⁻¹ ∈ KC ε := by
      show IsUnit (g * (posPart g)⁻¹) ∧ g * (posPart g)⁻¹ * Jm ε = Jm ε * (g * (posPart g)⁻¹)
      refine ⟨⟨⟨g * (posPart g)⁻¹, star (g * (posPart g)⁻¹),
        Matrix.mem_unitaryGroup_iff.1 hkK.1, Matrix.mem_unitaryGroup_iff'.1 hkK.1⟩, rfl⟩, hkK.2⟩
    have hp0U : (ofL n).symm (posPart g) ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} :=
      hPD _ hpd
    refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
    have hA : AnalyticAt ℂ (fun y => ⟪u, τ (projJ ε y) (b i)⟫_ℂ) (g * (posPart g)⁻¹) :=
      analyticAt_comp_projJ (f := fun M => ⟪u, τ M (b i)⟫_ℂ) (htau.2.2.1 u (b i)) hkKC
    have hBd : DifferentiableOn ℂ (fun x : Fin n → Fin n → ℂ => ⟪b i, ps ε lam τ w (Matrix.of x) v⟫_ℂ)
        {z | Matrix.of z ∈ U1 ε} :=
      (innerSL ℂ (b i)).differentiable.comp_differentiableOn (hpsd.clm_apply (differentiableOn_const v))
    have hBa : AnalyticAt ℂ (fun x : Fin n → Fin n → ℂ => ⟪b i, ps ε lam τ w (Matrix.of x) v⟫_ℂ)
        ((ofL n).symm (posPart g)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hBd (hUo.mem_nhds hp0U)
    exact (AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => Matrix.of z * (posPart (Matrix.of z))⁻¹)
      hA.restrictScalars hk).mul
      (AnalyticAt.comp (f := fun z : Fin n → Fin n → ℂ => (ofL n).symm (posPart (Matrix.of z)))
        hBa.restrictScalars hp)
  · refine Filter.Eventually.of_forall (fun z hz => ?_)
    have hc := (unitPart_mem hz).2
    simp only [Psi, ContinuousLinearMap.comp_apply]
    conv_lhs => rw [← b.sum_repr' (ps ε lam τ w (posPart (Matrix.of z)) v)]
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, inner_smul_right, projJ_of_comm hc]
    exact mul_comm _ _

/- English proof (translation)
The claim follows from `psiAnalytic_of_psBasic GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one`.
-/
theorem psiAnalytic : PsiAnalytic := psiAnalytic_of_psBasic GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one

end GlobalTheory.Dec
