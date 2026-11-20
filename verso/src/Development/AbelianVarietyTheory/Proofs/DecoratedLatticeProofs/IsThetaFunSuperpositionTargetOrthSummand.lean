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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposT

/- English proof (translation)
Establish `h` using `GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 y`. Rewrite `h` using `[add_zero]`. Take the linear combination `-h`.
-/
theorem symplOH_zero_left {D : D7} {S T : HSp D} (y : WO S T) : symplOH S T 0 y = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 y
  rw [add_zero] at h
  linear_combination -h

/- English proof (translation)
Establish `h` using `GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0`. Rewrite `h` using `[add_zero]`. Take the linear combination `-h`.
-/
theorem symplOH_zero_right {D : D7} {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0
  rw [add_zero] at h
  linear_combination -h

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`.
-/
theorem psi_neg_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

/- English proof (translation)
Rewrite using `[o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`.
-/
theorem symplOH_resT_symm {D : D7} {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u u' : WO S A) (v v' : WO S B) :
    symplOH S T ((o.resT S).symm (u, v)) ((o.resT S).symm (u', v')) = symplOH S A u u' + symplOH S B v v' := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `D ψ hψ T A B S o F hF Ω _ μ k a hk ha`. Use `haveI : BorelSpace (Mx D B.rank S.rank) := ⟨rfl⟩`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Take `⟨-, -, i3, -⟩` from `GlobalTheory.MixModel.lattice_Mx D A.rank S.rank`. Use `haveI : FirstCountableTopology (WO S A) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3`.

Take `⟨C, hC⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF`. Use `set e := o.resT S with he`. Establish `hsplit : ∀ (u u' : WO S A) (v : WO S B), e.symm (u + u', v) = e.symm (u, v) + e.symm (u', 0)`. Introduce `u u' v`. Rewrite using `[← map_add, Prod.mk_add_mk, add_zero]`.

Establish `hmeas : ∀ (F' : WO S T → ℂ), Continuous F' → ∀ (c : WO S T) (u : WO S A), AEStronglyMeasurable (fun ξ => F' (e.symm (u, k ξ) + c)) μ`. Introduce `F' hF' c u`. Conclude with `((hF'.comp (((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).add continuous_const)).measurable.comp hk).aestronglyMeasurable`. Set `φ : WO S A →+ WO S T` to `e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (WO S A) (WO S B))`. Establish `hφ : ∀ u, φ u = e.symm (u, 0)` using `fun u => rfl`.

Establish `hφc : Continuous φ` using `(o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)`. Establish `hφmap : ∀ (R : Type) [CommRing R] (f : Formalism.L2.Theta.AE D →+* R) (u : WO S A), u.map f = 0 → (φ u).map f = 0`. Introduce `R _ f u hu`. Rewrite using `[hφ, he, o.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.map_mul, hu, Matrix.mul_zero]`. Use `⟨fun γ u => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hr : e.symm (ratW A S γ, 0) = ratW T S (o.iA * γ)`. Rewrite using `[he, o.resT_symm_apply, Matrix.mul_zero, add_zero]`. Conclude with `(rat_mul _ _).symm`. Establish `h1 : ∀ ξ, F (e.symm (ratW A S γ + u, k ξ)) = ψ (-(symplOH S A (ratW A S γ) u)) * F (e.symm (u, k ξ))`. Introduce `ξ`.

Rewrite using `[add_comm (ratW A S γ) u, hsplit, add_comm, hr, hF.quasi, ← hr, symplOH_resT_symm, symplOH_zero_left, add_zero]`. Repeatedly rewrite using `[h1]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hU, hl⟩` from `hF.level`. Use `⟨U.comap φ, hU.preimage hφc, fun u hu h0 => ?_⟩` and prove the remaining obligations. Establish `hl'` using `hl (φ u) hu (hφmap _ _ u h0)`. Use function extensionality and compare the values at `w`.

Simplify using `only [heisO]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`. Establish `h2` using `congrFun hl' (e.symm (w, k ξ))`.

Simplify using `only [heisO] at h2`. Rewrite `h2` using `[hφ, symplOH_resT_symm, symplOH_zero_right, add_zero, ← hsplit]`. Rewrite using `[mul_left_comm, h2]`. Use `continuous_of_dominated (bound := fun ξ => ‖a ξ‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_` and prove the remaining obligations. Use `hmeas F hF.cont 0 u` as an intermediate fact.

Simplify using `only [add_zero] at this`. Conclude with `ha.aestronglyMeasurable.mul this`. Conclude with `Filter.Eventually.of_forall fun ξ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)`.

Conclude with `Filter.Eventually.of_forall fun ξ => continuous_const.mul (hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)))`. Introduce `n L hLc hL0 w`. Take `⟨θ, hθ⟩` from `GlobalTheory.Member.exists_isInfFam_family D`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Set `L' : (Fin n → ℝ) →+ WO S T` to `φ.comp L`.

Establish `hL'c : Continuous L'` using `hφc.comp hLc`. Establish `hL'0 : ∀ t, (L' t).map (finPart D) = 0` using `fun t => hφmap _ _ _ (hL0 t)`. Set `M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S` to `((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)`. Set `N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW A S` to `((GlobalTheory.FockCompare.piW θ A S).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ A S).comp hLc)`. Establish `hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t)` using `fun t => (h.iota_pi (hL'0 t)).symm`.

Establish `hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ A S (N t)` using `fun t => (h.iota_pi (hL0 t)).symm`. Set `om` to `LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S A (GlobalTheory.FockCompare.piW θ A S w))`. Establish `key : ∀ t, (∫ x, a x * F (e.symm (w + L t, k x)) ∂μ) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) * ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ`. Introduce `t`. Establish `hph : ψ (-symplOH S A w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ))`.

Establish `e1 : -symplOH S A w (L t) = symplOH S A w (L (-t))`. Rewrite using `[map_neg]`. Use `GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := A) w (L t) (-L t)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, symplOH_zero_right]`. Take the linear combination `this`.

Rewrite using `[e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]`. Both sides reduce to the same expression. Rewrite using `[← hph, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [heisO]`.

Rewrite using `[← hM, hsplit]`. Establish `hs : symplOH S T (e.symm (w, k x)) (L' t) = symplOH S A w (L t)` using `by show symplOH S T (e.symm (w, k x)) (e.symm (L t, 0)) = _`. Rewrite using `[symplOH_resT_symm, symplOH_zero_right, add_zero]`. Rewrite using `[hs]`. Express the relevant statement in the definitionally equal form `a x * F (_ + L' t) = ψ (-symplOH S A w (L t)) * (a x * (ψ (symplOH S A w (L t)) * F (_ + L' t)))`.

Use `psi_neg_mul ψ (symplOH S A w (L t))` as an intermediate fact. Take the linear combination `(-(a x * F (e.symm (w, k x) + L' t))) * this`. Establish `hf : (fun t => (fun u => ∫ x, a x * F (e.symm (u, k x)) ∂μ) (w + L t)) = fun t => Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) * ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ`. Use function extensionality and compare the values at `key`. Rewrite using `[hf]`.

Use `ContDiff.mul ?_ ((GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)` and prove the remaining obligations. Conclude with `Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.comp (N.contDiff.comp contDiff_neg))))`. Conclude with `((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).measurable.comp hk`.
-/
theorem superpos_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  intro D ψ hψ T A B S o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (Mx D B.rank S.rank) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank S.rank
  haveI : FirstCountableTopology (WO S A) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  set e := o.resT S with he
  have hsplit : ∀ (u u' : WO S A) (v : WO S B), e.symm (u + u', v) = e.symm (u, v) + e.symm (u', 0) := by
    intro u u' v
    rw [← map_add, Prod.mk_add_mk, add_zero]
  have hmeas : ∀ (F' : WO S T → ℂ), Continuous F' → ∀ (c : WO S T) (u : WO S A),
      AEStronglyMeasurable (fun ξ => F' (e.symm (u, k ξ) + c)) μ := by
    intro F' hF' c u
    exact ((hF'.comp (((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).add
      continuous_const)).measurable.comp hk).aestronglyMeasurable

  let φ : WO S A →+ WO S T := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (WO S A) (WO S B))
  have hφ : ∀ u, φ u = e.symm (u, 0) := fun u => rfl
  have hφc : Continuous φ := (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)
  have hφmap : ∀ (R : Type) [CommRing R] (f : Formalism.L2.Theta.AE D →+* R) (u : WO S A), u.map f = 0 → (φ u).map f = 0 := by
    intro R _ f u hu
    rw [hφ, he, o.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.map_mul, hu, Matrix.mul_zero]
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    have hr : e.symm (ratW A S γ, 0) = ratW T S (o.iA * γ) := by
      rw [he, o.resT_symm_apply, Matrix.mul_zero, add_zero]
      exact (rat_mul _ _).symm
    have h1 : ∀ ξ, F (e.symm (ratW A S γ + u, k ξ)) =
        ψ (-(symplOH S A (ratW A S γ) u)) * F (e.symm (u, k ξ)) := by
      intro ξ
      rw [add_comm (ratW A S γ) u, hsplit, add_comm, hr, hF.quasi, ← hr, symplOH_resT_symm, symplOH_zero_left, add_zero]
    simp_rw [h1]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap φ, hU.preimage hφc, fun u hu h0 => ?_⟩
    have hl' := hl (φ u) hu (hφmap _ _ u h0)
    funext w
    simp only [heisO]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    have h2 := congrFun hl' (e.symm (w, k ξ))
    simp only [heisO] at h2
    rw [hφ, symplOH_resT_symm, symplOH_zero_right, add_zero, ← hsplit] at h2
    rw [mul_left_comm, h2]
  ·
    refine continuous_of_dominated (bound := fun ξ => ‖a ξ‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · have := hmeas F hF.cont 0 u
      simp only [add_zero] at this
      exact ha.aestronglyMeasurable.mul this
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun ξ => continuous_const.mul
        (hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := φ.comp L
    have hL'c : Continuous L' := hφc.comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => hφmap _ _ _ (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW A S :=
      ((GlobalTheory.FockCompare.piW θ A S).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ A S).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ A S (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S A (GlobalTheory.FockCompare.piW θ A S w))
    have key : ∀ t, (∫ x, a x * F (e.symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH S A w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH S A w (L t) = symplOH S A w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := A) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, hsplit]
      have hs : symplOH S T (e.symm (w, k x)) (L' t) = symplOH S A w (L t) := by
        show symplOH S T (e.symm (w, k x)) (e.symm (L t, 0)) = _
        rw [symplOH_resT_symm, symplOH_zero_right, add_zero]
      rw [hs]
      change a x * F (_ + L' t) = ψ (-symplOH S A w (L t)) * (a x * (ψ (symplOH S A w (L t)) * F (_ + L' t)))
      have := psi_neg_mul ψ (symplOH S A w (L t))
      linear_combination (-(a x * F (e.symm (w, k x) + L' t))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F (e.symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposT

end
