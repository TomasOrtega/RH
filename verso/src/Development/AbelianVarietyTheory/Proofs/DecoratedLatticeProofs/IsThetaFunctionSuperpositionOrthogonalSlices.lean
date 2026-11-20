import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionRealStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposS

variable {D : D7}

/- English proof (translation)
Simplify using `using GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0`.
-/
theorem symplOH_zero_right {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0

/- English proof (translation)
Simplify using `using GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 x`.
-/
theorem symplOH_zero_left {S T : HSp D} (x : WO S T) : symplOH S T 0 x = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 x

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`.
-/
theorem psi_neg_mul (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

variable {S A B T : HSp D} (o : OrthDec S A B)

/- English proof (translation)
Rewrite using `[← map_add]`. Simplify using the standard rewrite rules.
-/
theorem symm_add (r u : WO A T) (y : WO B T) :
    (o.resS T).symm (u + r, y) = (o.resS T).symm (u, y) + (o.resS T).symm (r, 0) := by
  rw [← map_add]; simp

/- English proof (translation)
Rewrite using `[o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`. Simplify using `[symplOH_zero_right]`.
-/
theorem sympl_ext_right (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (u, y)) ((o.resS T).symm (r, 0)) = symplOH A T u r := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_right]

/- English proof (translation)
Rewrite using `[o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`. Simplify using `[symplOH_zero_left]`.
-/
theorem sympl_ext_left (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (r, 0)) ((o.resS T).symm (u, y)) = symplOH A T r u := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_left]

def ext0 (T : HSp D) : WO A T →+ WO S T := (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matrixExtendByZero_apply (r : WO A T) : ext0 o T r = (o.resS T).symm (r, 0) := rfl

/- English proof (translation)
The claim follows from `(o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)`.
-/
theorem continuous_wittExtendByZero : Continuous (ext0 o T) :=
  (o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)

/- English proof (translation)
Rewrite using `[matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.map_mul, h, Matrix.zero_mul]`.
-/
theorem matrixExtendByZero_map {R : Type} [Semiring R] (f : AE D →+* R) (r : WO A T) (h : r.map f = 0) : (ext0 o T r).map f = 0 := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.map_mul, h, Matrix.zero_mul]

/- English proof (translation)
Rewrite using `[matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, ratW, ratW, rat, Matrix.map_mul]`.
-/
theorem homExtensionByZeroOrthDecomp_rational (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) : ext0 o T (ratW T A γ) = ratW T S (γ * o.qA) := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, ratW, ratW, rat, Matrix.map_mul]

end GlobalTheory.SuperposS

namespace GlobalTheory.SuperposS

/- English proof (translation)
Introduce `D ψ hψ S A B T o F hF Ω _ μ k a hk ha`. Use `haveI : BorelSpace (WO B T) := ⟨rfl⟩`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Take `⟨C, hC⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF`. Establish `hFm : ∀ u : WO A T, Measurable fun w => F ((o.resS T).symm (u, k w))` using `fun u => (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id))).measurable.comp hk`.

Use `⟨fun γ u => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Establish `e : ∀ w, a w * F ((o.resS T).symm (ratW T A γ + u, k w)) = ψ (-symplOH A T (ratW T A γ) u) * (a w * F ((o.resS T).symm (u, k w)))`. Introduce `w`. Rewrite using `[add_comm, symm_add, add_comm, ← matrixExtendByZero_apply, homExtensionByZeroOrthDecomp_rational, hF.quasi, ← homExtensionByZeroOrthDecomp_rational, matrixExtendByZero_apply, sympl_ext_left]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Conclude with `integral_const_mul _ _`. Take `⟨U, hU, hl⟩` from `hF.level`. Use `⟨U.comap (ext0 o T), hU.preimage (continuous_wittExtendByZero o), fun u hu h0 => ?_⟩` and prove the remaining obligations.

Establish `hj` using `hl _ hu (matrixExtendByZero_map o _ u h0)`. Use function extensionality and compare the values at `v`. Simplify using `only [heisO]`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations.

Simplify using `only []`. Establish `e` using `congrFun hj ((o.resS T).symm (v, k w))`. Simplify using `only [heisO] at e`. Rewrite using `[symm_add, ← matrixExtendByZero_apply]`. Use `conv_rhs => rw [← e]`.

Rewrite using `[matrixExtendByZero_apply, sympl_ext_right]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨-, -, i3, -⟩` from `GlobalTheory.MixModel.lattice_Mx D T.rank A.rank`. Use `haveI : FirstCountableTopology (WO A T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3`. Use `continuous_of_dominated (bound := fun w => ‖a w‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_` and prove the remaining obligations.

Conclude with `ha.aestronglyMeasurable.mul (hFm u).aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun w => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)`. Use `Filter.Eventually.of_forall fun w => ?_` and prove the remaining obligations.

Conclude with `continuous_const.mul (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)))`. Introduce `n L hLc hL0 w`. Take `⟨θ, hθ⟩` from `GlobalTheory.Member.exists_isInfFam_family D`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Set `L' : (Fin n → ℝ) →+ WO S T` to `(ext0 o T).comp L`.

Establish `hL'c : Continuous L'` using `(continuous_wittExtendByZero o).comp hLc`. Establish `hL'0 : ∀ t, (L' t).map (finPart D) = 0` using `fun t => matrixExtendByZero_map o _ (L t) (hL0 t)`. Set `M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S` to `((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)`. Set `N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T A` to `((GlobalTheory.FockCompare.piW θ T A).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T A).comp hLc)`. Establish `hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t)` using `fun t => (h.iota_pi (hL'0 t)).symm`.

Establish `hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ T A (N t)` using `fun t => (h.iota_pi (hL0 t)).symm`. Set `om` to `LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO A T (GlobalTheory.FockCompare.piW θ T A w))`. Establish `key : ∀ t, (∫ x, a x * F ((o.resS T).symm (w + L t, k x)) ∂μ) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) * ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ`. Introduce `t`. Establish `hph : ψ (-symplOH A T w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ))`.

Establish `e1 : -symplOH A T w (L t) = symplOH A T w (L (-t))`. Rewrite using `[map_neg]`. Use `GlobalTheory.OrientedHeis.symplOH_add_right (S := A) (T := T) w (L t) (-L t)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, symplOH_zero_right]`. Take the linear combination `this`.

Rewrite using `[e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]`. Both sides reduce to the same expression. Rewrite using `[← hph, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [heisO]`.

Rewrite using `[← hM, symm_add, ← matrixExtendByZero_apply]`. Use `show _ = _ * (a x * (ψ (symplOH S T ((o.resS T).symm (w, k x)) ((o.resS T).symm (L t, 0))) * _))`. Rewrite using `[sympl_ext_right]`. Express the relevant statement in the definitionally equal form `a x * F (_ + ext0 o T (L t)) = ψ (-symplOH A T w (L t)) * (a x * (ψ (symplOH A T w (L t)) * F (_ + ext0 o T (L t))))`. Use `psi_neg_mul ψ (symplOH A T w (L t))` as an intermediate fact.

Take the linear combination `(-(a x * F ((o.resS T).symm (w, k x) + (ext0 o T) (L t)))) * this`. Establish `hf : (fun t => (fun u => ∫ x, a x * F ((o.resS T).symm (u, k x)) ∂μ) (w + L t)) = fun t => Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) * ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ`. Use function extensionality and compare the values at `key`. Rewrite using `[hf]`. Use `ContDiff.mul ?_ ((GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)` and prove the remaining obligations.

Conclude with `Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.comp (N.contDiff.comp contDiff_neg))))`. Conclude with `((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id)).measurable.comp hk`.
-/
theorem superpos_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  intro D ψ hψ S A B T o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hFm : ∀ u : WO A T, Measurable fun w => F ((o.resS T).symm (u, k w)) := fun u =>
    (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id))).measurable.comp hk
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    beta_reduce
    have e : ∀ w, a w * F ((o.resS T).symm (ratW T A γ + u, k w)) =
        ψ (-symplOH A T (ratW T A γ) u) * (a w * F ((o.resS T).symm (u, k w))) := by
      intro w
      rw [add_comm, symm_add, add_comm, ← matrixExtendByZero_apply, homExtensionByZeroOrthDecomp_rational, hF.quasi, ← homExtensionByZeroOrthDecomp_rational, matrixExtendByZero_apply, sympl_ext_left]
      ring
    simp_rw [e]
    exact integral_const_mul _ _
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap (ext0 o T), hU.preimage (continuous_wittExtendByZero o), fun u hu h0 => ?_⟩
    have hj := hl _ hu (matrixExtendByZero_map o _ u h0)
    funext v
    simp only [heisO]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    have e := congrFun hj ((o.resS T).symm (v, k w))
    simp only [heisO] at e
    rw [symm_add, ← matrixExtendByZero_apply]
    conv_rhs => rw [← e]
    rw [matrixExtendByZero_apply, sympl_ext_right]
    ring
  ·
    obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
    haveI : FirstCountableTopology (WO A T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
    refine continuous_of_dominated (bound := fun w => ‖a w‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · exact ha.aestronglyMeasurable.mul (hFm u).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun w => ?_
      exact continuous_const.mul (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := (ext0 o T).comp L
    have hL'c : Continuous L' := (continuous_wittExtendByZero o).comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => matrixExtendByZero_map o _ (L t) (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T A :=
      ((GlobalTheory.FockCompare.piW θ T A).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T A).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ T A (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO A T (GlobalTheory.FockCompare.piW θ T A w))
    have key : ∀ t, (∫ x, a x * F ((o.resS T).symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH A T w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH A T w (L t) = symplOH A T w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := A) (T := T) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, symm_add, ← matrixExtendByZero_apply]
      show _ = _ * (a x * (ψ (symplOH S T ((o.resS T).symm (w, k x)) ((o.resS T).symm (L t, 0))) * _))
      rw [sympl_ext_right]
      change a x * F (_ + ext0 o T (L t)) = ψ (-symplOH A T w (L t)) * (a x * (ψ (symplOH A T w (L t)) * F (_ + ext0 o T (L t))))
      have := psi_neg_mul ψ (symplOH A T w (L t))
      linear_combination (-(a x * F ((o.resS T).symm (w, k x) + (ext0 o T) (L t)))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F ((o.resS T).symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposS

end
