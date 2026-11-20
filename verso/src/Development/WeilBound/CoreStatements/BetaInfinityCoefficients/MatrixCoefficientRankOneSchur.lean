import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

namespace MainStatements.BetaInf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.QuantumDeterminants MeasureTheory Matrix
open scoped InnerProductSpace ComplexConjugate

noncomputable section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section side

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def sideF (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (a : Wp)
    (p : Mt k r × Mt k r) : ℂ :=
  ⟪w0, σ (Matrix.of p.2 * Matrix.of p.1) w0⟫_ℂ * star (psi k r z cStd (Matrix.of p.2)) * ⟪a, π (Matrix.of p.1)⁻¹ a⟫_ℂ

def skew (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (p.1, P.B7.mulM (P.B7.mulM (P.B7.invM p.1) p.2) p.1)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (P.MatrixMultiplicationContinuity.uw_inv hh).2.2`.
-/
theorem inv_inv_uw {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹⁻¹ = h :=
  Matrix.inv_eq_right_inv (P.MatrixMultiplicationContinuity.uw_inv hh).2.2

/- English proof (translation)
Use `P.B7.sf hW` as an intermediate fact. Use `P.B7.sf hN` as an intermediate fact. Use `MeasurePreserving.skew_product (f := id) (MeasurePreserving.id μW) (g := fun h n => P.B7.mulM (P.B7.mulM (P.B7.invM h) n) h) ?_ ?_` and prove the remaining obligations. Conclude with `P.B7.meas_mulM (P.B7.meas_mulM (P.B7.measurable_invM.comp measurable_fst) measurable_snd) measurable_fst`. Use `filter_upwards [P.B7.ae_mem hW] with h hh`.

Establish `e : (fun n => P.B7.mulM (P.B7.mulM (P.B7.invM h) n) h) = conjM (Matrix.of h : Mx k r)⁻¹`. Use function extensionality and compare the values at `n`. Unfold `conjM`. Rewrite using `[inv_inv_uw hh]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `hc _ (P.MatrixMultiplicationContinuity.uw_inv hh).1`.
-/
theorem skew_mp {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} (hW : B.IsHaarOn (UWset k r z) μW)
    (hN : B.IsHaarOn (Nset k r) μN) (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) :
    MeasurePreserving (skew (k := k) (r := r)) (μW.prod μN) (μW.prod μN) := by
  have := P.B7.sf hW
  have := P.B7.sf hN
  refine MeasurePreserving.skew_product (f := id) (MeasurePreserving.id μW)
    (g := fun h n => P.B7.mulM (P.B7.mulM (P.B7.invM h) n) h) ?_ ?_
  · exact P.B7.meas_mulM (P.B7.meas_mulM (P.B7.measurable_invM.comp measurable_fst) measurable_snd) measurable_fst
  · filter_upwards [P.B7.ae_mem hW] with h hh
    have e : (fun n => P.B7.mulM (P.B7.mulM (P.B7.invM h) n) h) = conjM (Matrix.of h : Mx k r)⁻¹ := by
      funext n
      unfold conjM
      rw [inv_inv_uw hh]
      rfl
    rw [e]
    exact hc _ (P.MatrixMultiplicationContinuity.uw_inv hh).1

/- English proof (translation)
Use `P.B7.sf hW` as an intermediate fact. Use `P.B7.sf hN` as an intermediate fact. Use `set L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ Wp a) with hL`. Establish `hLv : L ((innerSL ℂ a).smulRight a) = ((‖a‖ ^ 4 : ℝ) : ℂ)`. Simplify using `only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Simplify using `only [RCLike.ofReal_eq_complex_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : Integrable (beInt z cStd π σ w0 w0) (μW.prod μN)`. Assume the negation of the conclusion as `hn`.

Establish `h0 : be z cStd π σ μW μN w0 w0 = 0` using `integral_undef hn`. Rewrite `h0` using `[hbe]`. Rewrite `hLv` using `[h0, map_zero]`. Establish `: (‖a‖ ^ 4 : ℝ) = 0` using `by exact_mod_cast hLv.symm`. Conclude with `ha (norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))`.

Establish `hG : Integrable (fun p => L (beInt z cStd π σ w0 w0 p)) (μW.prod μN)` using `L.integrable_comp hint`. Establish `hGi : ∫ p, L (beInt z cStd π σ w0 w0 p) ∂(μW.prod μN) = ((‖a‖ ^ 4 : ℝ) : ℂ)`. Rewrite using `[L.integral_comp_comm hint, ← hLv, ← hbe]`. Both sides reduce to the same expression. Establish `hT` using `skew_mp hW hN hc`.

Establish `hae : sideF z π σ w0 a =ᵐ[μW.prod μN] (fun p => L (beInt z cStd π σ w0 w0 p)) ∘ skew` using `by filter_upwards [Measure.quasiMeasurePreserving_fst.ae (P.B7.ae_mem hW), Measure.quasiMeasurePreserving_snd.ae (P.B7.ae_mem hN)] with p hh hn`. Take `⟨hi, h1, h2⟩` from `P.MatrixMultiplicationContinuity.uw_inv hh`. Establish `em : (Matrix.of (skew p).2 : Mx k r) = (Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1` using `rfl`. Establish `e1 : (Matrix.of (skew p).1 : Mx k r) = Matrix.of p.1` using `rfl`. Establish `eψ : psi k r z cStd ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1) = psi k r z cStd (Matrix.of p.2)`.

Use `(Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ hi _ hn).2` as an intermediate fact. Rewrite `this` using `[inv_inv_uw hh]`. Unfold `psi`. Rewrite using `[this]`. Establish `eh : (Matrix.of p.1 : Mx k r) * ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1) = Matrix.of p.2 * Matrix.of p.1`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Simplify using `only [Function.comp_apply, beInt, em, e1, eψ, eh, hL, sideF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, _root_.smul_apply, innerSL_apply_apply, inner_smul_right]`. Use `⟨((hT.integrable_comp hG.aestronglyMeasurable).2 hG).congr hae.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, ← hGi]`. Establish `hm` using `integral_map (μ := μW.prod μN) hT.measurable.aemeasurable (f := fun p => L (beInt z cStd π σ w0 w0 p)) (by rw [hT.map_eq]; exact hG.aestronglyMeasurable)`.

Rewrite `hm` using `[hT.map_eq]`. Conclude with `hm.symm`.
-/
theorem side_int [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN)
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 : H) (a : Wp) (ha : a ≠ 0) (hbe : be z cStd π σ μW μN w0 w0 = (innerSL ℂ a).smulRight a) :
    Integrable (sideF z π σ w0 a) (μW.prod μN) ∧ ∫ p, sideF z π σ w0 a p ∂(μW.prod μN) = ((‖a‖ ^ 4 : ℝ) : ℂ) := by
  have := P.B7.sf hW
  have := P.B7.sf hN
  set L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ Wp a) with hL
  have hLv : L ((innerSL ℂ a).smulRight a) = ((‖a‖ ^ 4 : ℝ) : ℂ) := by
    simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    simp only [RCLike.ofReal_eq_complex_ofReal]
    ring
  have hint : Integrable (beInt z cStd π σ w0 w0) (μW.prod μN) := by
    by_contra hn
    have h0 : be z cStd π σ μW μN w0 w0 = 0 := integral_undef hn
    rw [hbe] at h0
    rw [h0, map_zero] at hLv
    have : (‖a‖ ^ 4 : ℝ) = 0 := by exact_mod_cast hLv.symm
    exact ha (norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  have hG : Integrable (fun p => L (beInt z cStd π σ w0 w0 p)) (μW.prod μN) := L.integrable_comp hint
  have hGi : ∫ p, L (beInt z cStd π σ w0 w0 p) ∂(μW.prod μN) = ((‖a‖ ^ 4 : ℝ) : ℂ) := by
    rw [L.integral_comp_comm hint, ← hLv, ← hbe]
    rfl
  have hT := skew_mp hW hN hc
  have hae : sideF z π σ w0 a =ᵐ[μW.prod μN] (fun p => L (beInt z cStd π σ w0 w0 p)) ∘ skew := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (P.B7.ae_mem hW),
      Measure.quasiMeasurePreserving_snd.ae (P.B7.ae_mem hN)] with p hh hn
    obtain ⟨hi, h1, h2⟩ := P.MatrixMultiplicationContinuity.uw_inv hh
    have em : (Matrix.of (skew p).2 : Mx k r) = (Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 := rfl
    have e1 : (Matrix.of (skew p).1 : Mx k r) = Matrix.of p.1 := rfl
    have eψ : psi k r z cStd ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1) = psi k r z cStd (Matrix.of p.2) := by
      have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ hi _ hn).2
      rw [inv_inv_uw hh] at this
      unfold psi
      rw [this]
    have eh : (Matrix.of p.1 : Mx k r) * ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1) =
        Matrix.of p.2 * Matrix.of p.1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Function.comp_apply, beInt, em, e1, eψ, eh, hL, sideF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, _root_.smul_apply, innerSL_apply_apply, inner_smul_right]
  refine ⟨((hT.integrable_comp hG.aestronglyMeasurable).2 hG).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, ← hGi]
  have hm := integral_map (μ := μW.prod μN) hT.measurable.aemeasurable
    (f := fun p => L (beInt z cStd π σ w0 w0 p)) (by rw [hT.map_eq]; exact hG.aestronglyMeasurable)
  rw [hT.map_eq] at hm
  exact hm.symm

end side

section both

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rk1 (c : ℝ) (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (a : Wp) (a' : Wq) (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  (c : ℂ) • (innerSL ℂ a').smulRight (⟪w0, σ g w0⟫_ℂ • a)

/- English proof (translation)
Rewrite using `[P.B6.hilbert_schmidt_inner_basis_sum]`. Establish `hs : ⟪a', A' a'⟫_ℂ = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, a'⟫_ℂ * ⟪a', A' (stdOrthonormalBasis ℂ Wq i)⟫_ℂ` using `by conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' a'] conv_lhs => enter [2]; rw [(stdOrthonormalBasis ℂ Wq).sum_repr' a']`. Rewrite using `[map_sum, inner_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_right]`.

Rewrite using `[hs, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.comp_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_conj_symm, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hsInner_rankOne (A : Wp →L[ℂ] Wp) (A' : Wq →L[ℂ] Wq) (a : Wp) (a' : Wq) (x y : ℂ) (c : ℝ) :
    B.hsInner (A.comp (((c : ℂ) • (innerSL ℂ a').smulRight (x • a)).comp A'))
        ((c : ℂ) • (innerSL ℂ a').smulRight (y • a)) =
      (c : ℂ) ^ 2 * (x * star y) * (⟪a, A a⟫_ℂ * ⟪a', A' a'⟫_ℂ) := by
  rw [P.B6.hilbert_schmidt_inner_basis_sum]
  have hs : ⟪a', A' a'⟫_ℂ = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, a'⟫_ℂ * ⟪a', A' (stdOrthonormalBasis ℂ Wq i)⟫_ℂ := by
    conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' a']
    conv_lhs => enter [2]; rw [(stdOrthonormalBasis ℂ Wq).sum_repr' a']
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, inner_smul_right]
  rw [hs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_conj_symm,
    Complex.star_def]
  ring

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `B.xiTau B.lam psi`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem xi_one (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau B.lam psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hp`. Use `set s : Mx k r := Matrix.of p.1.2 * Matrix.of p.1.1 with hs`. Use `set s' : Mx k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'`. Establish `hsG : s ∈ UH (Hpk k r)` using `P.DDSmoothness.uh_mul h2.1 h1.1`. Establish `hsG' : s' ∈ UH (Hpk k r)` using `P.DDSmoothness.uh_mul h4.1 h3.1`.

Take `⟨hsi, hss, hss2⟩` from `P.MatrixMultiplicationContinuity.uh_inv hsG`. Establish `hsii : s⁻¹⁻¹ = s` using `Matrix.inv_eq_right_inv hss2`. Establish `hPh : B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p = (c : ℂ) ^ 2 * (⟪a, D.π (Matrix.of p.1.1) a⟫_ℂ * ⟪a', D.π' (Matrix.of p.2.1)⁻¹ a'⟫_ℂ) * (⟪w0, σ s' w0⟫_ℂ * ⟪σ s w0, w0⟫_ℂ / (d : ℂ))`. Unfold `B.Ph`. Rewrite using `[← hS, ← integral_const_mul]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [P.B7.ae_mem D.haarG] with g hg`. Establish `e : B.sgs p (Matrix.of g) = s⁻¹ * (Matrix.of g * s')`. Unfold `B.sgs`. Rewrite using `[hs, hs', Matrix.mul_inv_rev]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `e2 : ⟪w0, σ (B.sgs p (Matrix.of g)) w0⟫_ℂ = ⟪σ s w0, σ (Matrix.of g) (σ s' w0)⟫_ℂ`. Rewrite using `[e, P.TranslationBesselVanishing.sigma_mul hσ hsi (P.DDSmoothness.uh_mul hg hsG'), P.TranslationBesselVanishing.sigma_mul hσ hg hsG', ContinuousLinearMap.comp_apply, P.MatrixMultiplicationContinuity.sigma_inner hσ hsi, hsii]`. Both sides reduce to the same expression. Unfold `B.rho rk1`.

Rewrite using `[hsInner_rankOne, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hπ : conj ⟪a, D.π (Matrix.of p.1.1)⁻¹ a⟫_ℂ = ⟪a, D.π (Matrix.of p.1.1) a⟫_ℂ`. Take `⟨hi, hhi, -⟩` from `P.MatrixMultiplicationContinuity.uw_inv h1`. Establish `hiso : ∀ x y, ⟪D.π (Matrix.of p.1.1) x, D.π (Matrix.of p.1.1) y⟫_ℂ = ⟪x, y⟫_ℂ` using `(LinearMap.norm_map_iff_inner_map_map ((D.π (Matrix.of p.1.1) : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (D.π_unitary _ h1)`.

Establish `e : D.π (Matrix.of p.1.1) (D.π (Matrix.of p.1.1)⁻¹ a) = a`. Use `congrArg (fun T : Wp →L[ℂ] Wp => T a) (D.π_rep.2 _ h1 _ hi)` as an intermediate fact. Simplify using `only [hhi, D.π_rep.1] at this`. Conclude with `this.symm`. Rewrite using `[inner_conj_symm, ← hiso, e]`.

Rewrite using `[hPh, xi_one]`. Unfold `sideF`. Rewrite using `[map_mul, map_mul, hπ, inner_conj_symm, ← hs, ← hs', Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem matrixCoefficient_rankOne_schur [CompleteSpace H] (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H)
    (a : Wp) (a' : Wq) (c d : ℝ)
    (hS : ∀ v w v' w' : H,
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂D.μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (p : B.SS k r) (hp : D.inSS p) :
    B.xiTau D (1, 1) p * B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p =
      (c : ℂ) ^ 2 / d * (conj (sideF D.z D.π σ w0 a p.1) * sideF D.z' D.π' σ w0 a' p.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set s : Mx k r := Matrix.of p.1.2 * Matrix.of p.1.1 with hs
  set s' : Mx k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'
  have hsG : s ∈ UH (Hpk k r) := P.DDSmoothness.uh_mul h2.1 h1.1
  have hsG' : s' ∈ UH (Hpk k r) := P.DDSmoothness.uh_mul h4.1 h3.1
  obtain ⟨hsi, hss, hss2⟩ := P.MatrixMultiplicationContinuity.uh_inv hsG
  have hsii : s⁻¹⁻¹ = s := Matrix.inv_eq_right_inv hss2
  have hPh : B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p =
      (c : ℂ) ^ 2 * (⟪a, D.π (Matrix.of p.1.1) a⟫_ℂ * ⟪a', D.π' (Matrix.of p.2.1)⁻¹ a'⟫_ℂ) *
        (⟪w0, σ s' w0⟫_ℂ * ⟪σ s w0, w0⟫_ℂ / (d : ℂ)) := by
    unfold B.Ph
    rw [← hS, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [P.B7.ae_mem D.haarG] with g hg
    have e : B.sgs p (Matrix.of g) = s⁻¹ * (Matrix.of g * s') := by
      unfold B.sgs
      rw [hs, hs', Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have e2 : ⟪w0, σ (B.sgs p (Matrix.of g)) w0⟫_ℂ = ⟪σ s w0, σ (Matrix.of g) (σ s' w0)⟫_ℂ := by
      rw [e, P.TranslationBesselVanishing.sigma_mul hσ hsi (P.DDSmoothness.uh_mul hg hsG'), P.TranslationBesselVanishing.sigma_mul hσ hg hsG',
        ContinuousLinearMap.comp_apply, P.MatrixMultiplicationContinuity.sigma_inner hσ hsi, hsii]
      rfl
    unfold B.rho rk1
    rw [hsInner_rankOne, e2]
    ring
  have hπ : conj ⟪a, D.π (Matrix.of p.1.1)⁻¹ a⟫_ℂ = ⟪a, D.π (Matrix.of p.1.1) a⟫_ℂ := by
    obtain ⟨hi, hhi, -⟩ := P.MatrixMultiplicationContinuity.uw_inv h1
    have hiso : ∀ x y, ⟪D.π (Matrix.of p.1.1) x, D.π (Matrix.of p.1.1) y⟫_ℂ = ⟪x, y⟫_ℂ :=
      (LinearMap.norm_map_iff_inner_map_map ((D.π (Matrix.of p.1.1) : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1
        (D.π_unitary _ h1)
    have e : D.π (Matrix.of p.1.1) (D.π (Matrix.of p.1.1)⁻¹ a) = a := by
      have := congrArg (fun T : Wp →L[ℂ] Wp => T a) (D.π_rep.2 _ h1 _ hi)
      simp only [hhi, D.π_rep.1] at this
      exact this.symm
    rw [inner_conj_symm, ← hiso, e]
  rw [hPh, xi_one]
  unfold sideF
  rw [map_mul, map_mul, hπ, inner_conj_symm, ← hs, ← hs', Complex.star_def, Complex.conj_conj]
  ring

/- English proof (translation)
Use `P.B7.sf D.haarW` as an intermediate fact. Use `P.B7.sf D.haarN` as an intermediate fact. Use `P.B7.sf D.haarW'` as an intermediate fact. Establish `hC` using `P.conjugation_invariance_every_setting k r Wp Wq D`. Take `⟨i1, e1⟩` from `side_int D.z_mem D.haarW D.haarN (fun h hh => hC h (Or.inl hh)) D.π σ w0 a ha hbe`.

Take `⟨i2, e2⟩` from `side_int D.z'_mem D.haarW' D.haarN (fun h hh => hC h (Or.inr hh)) D.π' σ w0 a' ha' hbe'`. Establish `i1' : Integrable (fun q => conj (sideF D.z D.π σ w0 a q)) (D.μW.prod D.μN)` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp i1`. Establish `hae : (fun p => B.xiTau D (1, 1) p * B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p) =ᵐ[D.μSS] fun p => (c : ℂ) ^ 2 / d * (conj (sideF D.z D.π σ w0 a p.1) * sideF D.z' D.π' σ w0 a' p.2)` using `by filter_upwards [P.B7.ae_inSS D] with p hp using matrixCoefficient_rankOne_schur D hσ w0 a a' c d hS p hp`. Use `⟨((i1'.mul_prod i2).const_mul _).congr hae.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, integral_const_mul]`.

Unfold `B.RealPlaceData.μSS`. Rewrite using `[integral_prod_mul (fun q => conj (sideF D.z D.π σ w0 a q)) (sideF D.z' D.π' σ w0 a'), integral_conj, e1, e2, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core [CompleteSpace H] [CompleteSpace Wp] [CompleteSpace Wq] (D : B.RealPlaceData k r Wp Wq)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) (a : Wp) (a' : Wq) (ha : a ≠ 0) (ha' : a' ≠ 0) (c d : ℝ)
    (hS : ∀ v w v' w' : H,
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂D.μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hbe : be D.z cStd D.π σ D.μW D.μN w0 w0 = (innerSL ℂ a).smulRight a)
    (hbe' : be D.z' cStd D.π' σ D.μW' D.μN w0 w0 = (innerSL ℂ a').smulRight a') :
    Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p) D.μSS ∧
      ∫ p, B.xiTau D (1, 1) p * B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p ∂D.μSS =
        ((c ^ 2 / d * (‖a‖ ^ 4 * ‖a'‖ ^ 4) : ℝ) : ℂ) := by
  have := P.B7.sf D.haarW
  have := P.B7.sf D.haarN
  have := P.B7.sf D.haarW'
  have hC := P.conjugation_invariance_every_setting k r Wp Wq D
  obtain ⟨i1, e1⟩ := side_int D.z_mem D.haarW D.haarN (fun h hh => hC h (Or.inl hh)) D.π σ w0 a ha hbe
  obtain ⟨i2, e2⟩ := side_int D.z'_mem D.haarW' D.haarN (fun h hh => hC h (Or.inr hh)) D.π' σ w0 a' ha' hbe'
  have i1' : Integrable (fun q => conj (sideF D.z D.π σ w0 a q)) (D.μW.prod D.μN) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp i1
  have hae : (fun p => B.xiTau D (1, 1) p * B.Ph D (rk1 c σ w0 a a') (rk1 c σ w0 a a') p) =ᵐ[D.μSS]
      fun p => (c : ℂ) ^ 2 / d * (conj (sideF D.z D.π σ w0 a p.1) * sideF D.z' D.π' σ w0 a' p.2) := by
    filter_upwards [P.B7.ae_inSS D] with p hp using matrixCoefficient_rankOne_schur D hσ w0 a a' c d hS p hp
  refine ⟨((i1'.mul_prod i2).const_mul _).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  unfold B.RealPlaceData.μSS
  rw [integral_prod_mul (fun q => conj (sideF D.z D.π σ w0 a q)) (sideF D.z' D.π' σ w0 a'), integral_conj, e1, e2,
    Complex.conj_ofReal]
  push_cast
  ring

end both

end

end MainStatements.BetaInf
