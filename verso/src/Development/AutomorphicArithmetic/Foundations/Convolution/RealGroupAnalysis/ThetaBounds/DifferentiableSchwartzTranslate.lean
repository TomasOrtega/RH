import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]`. Conclude with `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _`.
-/
private theorem infPart_add (a b : V4 F) : infPartPi (a + b) = infPartPi a + infPartPi b := by
  funext i
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

variable [IsTotallyReal F]

private noncomputable def ell : (Fin 4 → TR.Rinf F) →L[ℝ] (Fin 4 → mixedEmbedding.mixedSpace F) :=
  AddMonoidHom.toRealLinearMap
    { toFun := fun x => infPartPi fun i => TR.sInf F (x i)
      map_zero' := by
        funext i
        simp only [infPartPi, map_zero, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun x y => by
        have : (fun i => TR.sInf F ((x + y) i)) = (fun i => TR.sInf F (x i)) + fun i => TR.sInf F (y i) := by
          funext i
          simp only [Pi.add_apply, map_add]
        rw [this, infPart_add] }
    (continuous_pi fun i => (homeomorphMixedSpace F).continuous.comp
      ((TR.continuous_infEq F).comp (continuous_apply i)))

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨f, g, hg, rfl⟩` from `hG`. Establish `e : ∀ x : Fin 4 → TR.Rinf F, schwartzBruhatTensorPi f g (fun i => v i + TR.sInf F (x i)) = f (infPartPi v + ell x) * g (finPartPi v)`. Introduce `x`.

Establish `h1 : infPartPi (fun i => v i + TR.sInf F (x i)) = infPartPi v + ell x` using `infPart_add v fun i => TR.sInf F (x i)`. Establish `h2 : finPartPi (fun i => v i + TR.sInf F (x i)) = finPartPi v`. Use function extensionality and compare the values at `i`. Conclude with `add_zero (v i).2`. Simplify using `only [schwartzBruhatTensorPi, h1, h2]`.

Repeatedly rewrite using `[e]`. Conclude with `(f.differentiable.comp ((differentiable_const _).add ell.differentiable)).mul_const _`. Consider the case `zero => exact differentiable_const _`. Consider the case `add G H _ _ hG hH => exact hG.add hH`. Consider the case `smul c G _ hG => exact hG.const_smul c`.
-/
private theorem differentiable_schwartz_translate (v : V4 F) {Φ : V4 F → ℂ} (h : Φ ∈ schwartzBruhatPi F (Fin 4)) :
    Differentiable ℝ fun x : Fin 4 → TR.Rinf F => Φ fun i => v i + TR.sInf F (x i) := by
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : ∀ x : Fin 4 → TR.Rinf F, schwartzBruhatTensorPi f g (fun i => v i + TR.sInf F (x i)) =
        f (infPartPi v + ell x) * g (finPartPi v) := by
      intro x
      have h1 : infPartPi (fun i => v i + TR.sInf F (x i)) = infPartPi v + ell x :=
        infPart_add v fun i => TR.sInf F (x i)
      have h2 : finPartPi (fun i => v i + TR.sInf F (x i)) = finPartPi v := by
        funext i
        exact add_zero (v i).2
      simp only [schwartzBruhatTensorPi, h1, h2]
    simp_rw [e]
    exact (f.differentiable.comp ((differentiable_const _).add ell.differentiable)).mul_const _
  | zero => exact differentiable_const _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ _ O φ v x x' h0 hx`. Use `set G : (Fin 4 → TR.Rinf F) → ℂ := fun y => φ.1 fun i => v i + TR.sInf F (y i) with hG`. Establish `hd : DifferentiableAt ℝ G 0` using `differentiable_schwartz_translate v φ.2 0`. Establish `hF : HasFDerivAt G (fderiv ℝ G 0) (x 0)`. Rewrite using `[h0]`.

Conclude with `hd.hasFDerivAt`. Establish `hc : HasDerivAt (fun t => G (x t)) (fderiv ℝ G 0 x') 0` using `hF.comp_hasDerivAt 0 hx`. Establish `hb : ∀ i w, fderiv ℝ G 0 (Pi.single i (Pi.single w 1)) = (O.d w i φ).1 v`. Introduce `i w`. Use `set e : Fin 4 → TR.Rinf F := Pi.single i (Pi.single w 1) with he`.

Establish `hl : HasDerivAt (fun t : ℝ => t • e) e 0`. Simplify using `using (hasDerivAt_id (0 : ℝ)).smul_const e`. Establish `hF0 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • e)`. Rewrite using `[zero_smul]`. Conclude with `hd.hasFDerivAt`.

Establish `h1` using `hF0.comp_hasDerivAt (0 : ℝ) hl`. Establish `h2` using `O.d_spec w i φ v`. Establish `hfun : (fun t : ℝ => G (t • e)) = fun t : ℝ => φ.1 (v + Pi.single i (Fo.at1 w t))`. Use function extensionality and compare the values at `t`. Use `congrArg φ.1 ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Establish `: (t • e) j = Pi.single w t`. Use function extensionality and compare the values at `u`.

Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Simplify using `[he]`. Simplify using `[he, hu]`. Simplify using `[this, Fo.at1]`.

Establish `: (t • e) j = 0` using `by simp [he, hj]`. Simplify using `[this, hj]`. Conclude with `(HasDerivAt.unique (by simpa [Function.comp_def, hfun] using h1) h2)`. Establish `hs : x' = ∑ i, ∑ w, x' i w • (Pi.single i (Pi.single w 1) : Fin 4 → TR.Rinf F)`. Use function extensionality and compare the values at `i w`.

Establish `h1 : ∀ c, c ≠ i → (∑ u, x' c u • (Pi.single c (Pi.single u 1) : Fin 4 → TR.Rinf F)) i = 0`. Introduce `c hc`. Simplify using `[Finset.sum_apply, Pi.single_eq_of_ne hc.symm]`. Establish `h2 : (∑ u, x' i u • (Pi.single i (Pi.single u 1) : Fin 4 → TR.Rinf F)) i w = x' i w`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i (fun c _ hc => h1 c hc) (by simp), h2]`. Establish `key : fderiv ℝ G 0 x' = ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v` using `by conv_lhs => rw [hs]`. Simplify using `only [map_sum, map_smul, hb, Complex.real_smul]`. Rewrite using `[← key]`. Conclude with `hc`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.sDiff :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Fo.Ops F), SDiff O := by
  intro F _ _ _ O φ v x x' h0 hx
  set G : (Fin 4 → TR.Rinf F) → ℂ := fun y => φ.1 fun i => v i + TR.sInf F (y i) with hG
  have hd : DifferentiableAt ℝ G 0 := differentiable_schwartz_translate v φ.2 0
  have hF : HasFDerivAt G (fderiv ℝ G 0) (x 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hc : HasDerivAt (fun t => G (x t)) (fderiv ℝ G 0 x') 0 := hF.comp_hasDerivAt 0 hx
  have hb : ∀ i w, fderiv ℝ G 0 (Pi.single i (Pi.single w 1)) = (O.d w i φ).1 v := by
    intro i w
    set e : Fin 4 → TR.Rinf F := Pi.single i (Pi.single w 1) with he
    have hl : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hF0 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact hd.hasFDerivAt
    have h1 := hF0.comp_hasDerivAt (0 : ℝ) hl
    have h2 := O.d_spec w i φ v
    have hfun : (fun t : ℝ => G (t • e)) = fun t : ℝ => φ.1 (v + Pi.single i (Fo.at1 w t)) := by
      funext t
      refine congrArg φ.1 ?_
      funext j
      by_cases hj : j = i
      · subst hj
        have : (t • e) j = Pi.single w t := by
          funext u
          by_cases hu : u = w
          · subst hu
            simp [he]
          · simp [he, hu]
        simp [this, Fo.at1]
      · have : (t • e) j = 0 := by simp [he, hj]
        simp [this, hj]
    exact (HasDerivAt.unique (by simpa [Function.comp_def, hfun] using h1) h2)
  have hs : x' = ∑ i, ∑ w, x' i w • (Pi.single i (Pi.single w 1) : Fin 4 → TR.Rinf F) := by
    funext i w
    have h1 : ∀ c, c ≠ i → (∑ u, x' c u • (Pi.single c (Pi.single u 1) : Fin 4 → TR.Rinf F)) i = 0 := by
      intro c hc
      simp [Finset.sum_apply, Pi.single_eq_of_ne hc.symm]
    have h2 : (∑ u, x' i u • (Pi.single i (Pi.single u 1) : Fin 4 → TR.Rinf F)) i w = x' i w := by
      simp [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun c _ hc => h1 c hc) (by simp), h2]
  have key : fderiv ℝ G 0 x' = ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v := by
    conv_lhs => rw [hs]
    simp only [map_sum, map_smul, hb, Complex.real_smul]
  rw [← key]
  exact hc
