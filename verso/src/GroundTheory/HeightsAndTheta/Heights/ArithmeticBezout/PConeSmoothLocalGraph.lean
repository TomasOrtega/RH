import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSmoothLocalGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsHolomorphicImplicitGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `e1 : (fun z : Fin n → ℂ => eval z (C a)) = fun _ => a`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules.

Rewrite using `[e1]`. Use `hasFDerivAt_const (𝕜 := ℂ) a x` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`.

Establish `e1 : (fun z : Fin n → ℂ => eval z (p + q)) = fun z => eval z p + eval z q`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Use `(hp.add hq).congr_fderiv ?_` and prove the remaining obligations.

Use extensionality with `v`. Simplify using `[Finset.sum_add_distrib, add_mul]`. Consider the case `mul_X p i hp`. Establish `hfun : (fun z : Fin n → ℂ => eval z (p * X i)) = (fun z => eval z p) * (fun z => z i)`. Use function extensionality and compare the values at `z`.

Simplify using the standard rewrite rules. Rewrite using `[hfun]`. Use `(hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_` and prove the remaining obligations. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]`.

Simplify using `only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]`. Rewrite using `[add_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Apply the tactic sequence `by_cases hij : i = i <;> simp [mul_comm]`.
-/
theorem hasFDerivAt_eval_mvPolynomial (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun z : Fin n → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have e1 : (fun z : Fin n → ℂ => eval z (C a)) = fun _ => a := by
      funext z
      simp
    rw [e1]
    convert hasFDerivAt_const (𝕜 := ℂ) a x
    ext v
    simp
  | add p q hp hq =>
    have e1 : (fun z : Fin n → ℂ => eval z (p + q)) = fun z => eval z p + eval z q := by
      funext z
      simp
    rw [e1]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
    have hfun : (fun z : Fin n → ℂ => eval z (p * X i)) = (fun z => eval z p) * (fun z => z i) := by
      funext z
      simp
    rw [hfun]
    refine (hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pderiv_mul,
      pderiv_X, map_add, map_mul, eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · by_cases hij : i = i <;> simp [mul_comm]

def HermNorm.pointOfE (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  h.pointOfL.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HermNorm.pointOfE_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfE v = h.pointOf v := rfl

def HermNorm.pointOfC (h : HermNorm n) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HermNorm.pointOfC_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfC v = h.pointOf v := rfl

/- English proof (translation)
The claim follows from `(hasFDerivAt_eval_mvPolynomial q (h.pointOfC z)).comp z h.pointOfC.hasFDerivAt`.
-/
theorem hasFDerivAt_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w => eval (h.pointOf w) q)
      ((∑ j, eval (h.pointOf z) (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
        h.pointOfC) z :=
  (hasFDerivAt_eval_mvPolynomial q (h.pointOfC z)).comp z h.pointOfC.hasFDerivAt

/- English proof (translation)
Rewrite using `[(hasFDerivAt_eval_pointOf h q z).fderiv]`. Simplify using `[HermNorm.pointOfC_apply]`.
-/
theorem fderiv_eval_pointOf_apply (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (fun w => eval (h.pointOf w) q) z v =
      ∑ j, eval (h.pointOf z) (pderiv j q) * h.pointOf v j := by
  rw [(hasFDerivAt_eval_pointOf h q z).fderiv]
  simp [HermNorm.pointOfC_apply]

/- English proof (translation)
Establish `ha : AnalyticOnNhd ℂ (fun w => eval (h.pointOfC w) q) Set.univ` using `(AnalyticOnNhd.eval_mvPolynomial q).comp (h.pointOfC.analyticOnNhd Set.univ) (fun _ _ => Set.mem_univ _)`. Conclude with `contDiffOn_univ.1 (ha.contDiffOn uniqueDiffOn_univ)`.
-/
theorem contDiff_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ 1 (fun w => eval (h.pointOf w) q) := by
  have ha : AnalyticOnNhd ℂ (fun w => eval (h.pointOfC w) q) Set.univ :=
    (AnalyticOnNhd.eval_mvPolynomial q).comp (h.pointOfC.analyticOnNhd Set.univ)
      (fun _ _ => Set.mem_univ _)
  exact contDiffOn_univ.1 (ha.contDiffOn uniqueDiffOn_univ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coneTangent_eq_comap (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) :
    coneTangent h J z = (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf z)).comap
      (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := rfl

/- English proof (translation)
Rewrite using `[Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]`.
-/
theorem finrank_comap_equiv {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (φ : E ≃ₗ[ℂ] F) (S : Submodule ℂ F) :
    finrank ℂ (S.comap (φ : E →ₗ[ℂ] F)) = finrank ℂ S := by
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/- English proof (translation)
Introduce `n m h J hJ hdim y hy htan`. Establish `hpy : ∀ q ∈ J, eval (h.pointOf y) q = 0` using `hy`. Establish `htanp : finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf y)) = m`. Rewrite using `[← htan, coneTangent_eq_comap, finrank_comap_equiv]`. Take `⟨q, g, hqJ, hgp, htanq, hgen⟩` from `hGen n m J hJ hdim (h.pointOf y) hpy htanp`.

Use `set f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ := fun i w => eval (h.pointOf w) (q i) with hf`. Establish `hker : ∀ z, (⨅ i, LinearMap.ker (fderiv ℂ (f i) z : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) : Submodule ℂ (EuclideanSpace ℂ (Fin n))) = (polyTangent (Set.range q) (h.pointOf z)).comap (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))`. Introduce `z`. Use extensionality with `v`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_comap, LinearEquiv.coe_coe, HermNorm.pointOfE_apply, hf, fderiv_eval_pointOf_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `hv _ ⟨i, rfl⟩`. Conclude with `hv i`. Introduce `hv i`. Conclude with `hv _ ⟨i, rfl⟩`.

Establish `hfC : ∀ i, ContDiff ℂ 1 (f i)` using `fun i => contDiff_eval_pointOf h (q i)`. Use `set V : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (h.pointOf z) g ≠ 0} with hV`. Establish `hVo : IsOpen V` using `isOpen_ne_fun ((continuous_eval g).comp h.continuous_pointOf) continuous_const`. Establish `hfy : ∀ i, f i y = 0` using `fun i => hpy _ (hqJ i)`. Establish `hrank : finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) : Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m`.

Rewrite using `[hker, finrank_comap_equiv, htanq]`. Take `⟨e, Ω, Φ, U, hU, hyU, hUV, hΩ, hΦ, hG, htanG⟩` from `hImp n m f y V hfC hVo hgp hfy hrank`. Establish `hGC : graphPt e Φ '' Ω ⊆ coneSet h J`. Introduce `z hz`. Rewrite `hz` using `[hG]`.

Take `⟨hzU, hzq⟩` from `hz`. Establish `hgz : eval (h.pointOf z) g ≠ 0` using `hUV hzU`. Introduce `r hr`. Establish `hspan : Ideal.span (Set.range q) ≤ RingHom.ker (eval (h.pointOf z))` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hzq i)`. Establish `h0` using `hspan (hgen r hr)`.

Rewrite `h0` using `[RingHom.mem_ker, map_mul]`. Conclude with `(mul_eq_zero.1 h0).resolve_left hgz`. Use `⟨e, Ω, Φ, U, hU, hyU, ?_, hΩ, hΦ, hGC, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hzU⟩`. Rewrite using `[hG]`.

Conclude with `⟨hzU, fun i => hz _ (hqJ i)⟩`. Introduce `x hx`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[htanG x hx, hker, coneTangent_eq_comap]`. Introduce `v hv`.

Simplify using `only [Submodule.mem_comap] at hv ⊢`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hv (q i) (hqJ i)`. Introduce and unpack `_ ⟨v, rfl⟩`. Introduce `r hr`.

Simplify using `only [ContinuousLinearMap.coe_coe]`. Distinguish the cases in `hd : DifferentiableAt ℂ (graphPt e Φ) x`. Establish `hzero : (fun w => eval (h.pointOf w) r) ∘ graphPt e Φ =ᶠ[nhds x] fun _ => (0 : ℂ)` using `by filter_upwards [hΩ.mem_nhds hx] with w hw`. Conclude with `hGC ⟨w, hw, rfl⟩ r hr`. Establish `hD` using `hzero.fderiv_eq (𝕜 := ℂ)`.

Rewrite `hD` using `[fderiv_const_apply, fderiv_comp x (hasFDerivAt_eval_pointOf h r _).differentiableAt hd]`. Establish `hDv` using `congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ => L v) hD`. Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.zero_apply, ContinuousLinearMap.zero_apply, fderiv_eval_pointOf_apply] at hDv`. Conclude with `hDv`. Rewrite using `[fderiv_zero_of_not_differentiableAt hd]`.

Establish `h0 : h.pointOf 0 = 0` using `by simpa using h.pointOf_smul' 0 0`. Simplify using `[h0]`.
-/
theorem ConeSmoothLocalGraph.proof (hGen : PolyLocalGenerators.Statement)
    (hImp : HolomorphicImplicitGraph.Statement) : ConeSmoothLocalGraph.Statement := by
  intro n m h J hJ hdim y hy htan
  have hpy : ∀ q ∈ J, eval (h.pointOf y) q = 0 := hy
  have htanp : finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf y)) = m := by
    rw [← htan, coneTangent_eq_comap, finrank_comap_equiv]
  obtain ⟨q, g, hqJ, hgp, htanq, hgen⟩ := hGen n m J hJ hdim (h.pointOf y) hpy htanp
  set f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ := fun i w => eval (h.pointOf w) (q i) with hf
  have hker : ∀ z, (⨅ i, LinearMap.ker (fderiv ℂ (f i) z : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = (polyTangent (Set.range q) (h.pointOf z)).comap
        (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := by
    intro z
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_comap,
      LinearEquiv.coe_coe, HermNorm.pointOfE_apply, hf, fderiv_eval_pointOf_apply]
    constructor
    · rintro hv _ ⟨i, rfl⟩
      exact hv i
    · intro hv i
      exact hv _ ⟨i, rfl⟩
  have hfC : ∀ i, ContDiff ℂ 1 (f i) := fun i => contDiff_eval_pointOf h (q i)
  set V : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (h.pointOf z) g ≠ 0} with hV
  have hVo : IsOpen V :=
    isOpen_ne_fun ((continuous_eval g).comp h.continuous_pointOf) continuous_const
  have hfy : ∀ i, f i y = 0 := fun i => hpy _ (hqJ i)
  have hrank : finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m := by
    rw [hker, finrank_comap_equiv, htanq]
  obtain ⟨e, Ω, Φ, U, hU, hyU, hUV, hΩ, hΦ, hG, htanG⟩ := hImp n m f y V hfC hVo hgp hfy hrank
  have hGC : graphPt e Φ '' Ω ⊆ coneSet h J := by
    intro z hz
    rw [hG] at hz
    obtain ⟨hzU, hzq⟩ := hz
    have hgz : eval (h.pointOf z) g ≠ 0 := hUV hzU
    intro r hr
    have hspan : Ideal.span (Set.range q) ≤ RingHom.ker (eval (h.pointOf z)) :=
      Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hzq i)
    have h0 := hspan (hgen r hr)
    rw [RingHom.mem_ker, map_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hgz
  refine ⟨e, Ω, Φ, U, hU, hyU, ?_, hΩ, hΦ, hGC, ?_⟩
  · rintro z ⟨hz, hzU⟩
    rw [hG]
    exact ⟨hzU, fun i => hz _ (hqJ i)⟩
  · intro x hx
    apply le_antisymm
    · rw [htanG x hx, hker, coneTangent_eq_comap]
      intro v hv
      simp only [Submodule.mem_comap] at hv ⊢
      rintro _ ⟨i, rfl⟩
      exact hv (q i) (hqJ i)
    · rintro _ ⟨v, rfl⟩
      intro r hr
      simp only [ContinuousLinearMap.coe_coe]
      by_cases hd : DifferentiableAt ℂ (graphPt e Φ) x
      · have hzero : (fun w => eval (h.pointOf w) r) ∘ graphPt e Φ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
          filter_upwards [hΩ.mem_nhds hx] with w hw
          exact hGC ⟨w, hw, rfl⟩ r hr
        have hD := hzero.fderiv_eq (𝕜 := ℂ)
        rw [fderiv_const_apply, fderiv_comp x (hasFDerivAt_eval_pointOf h r _).differentiableAt hd] at hD
        have hDv := congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ => L v) hD
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.zero_apply,
          ContinuousLinearMap.zero_apply, fderiv_eval_pointOf_apply] at hDv
        exact hDv
      · rw [fderiv_zero_of_not_differentiableAt hd]
        have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
        simp [h0]

end

end GroundTheory.Heights₂.Heights
