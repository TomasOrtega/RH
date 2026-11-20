import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DifferentiableSchwartzTranslate
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def eR (w : InfinitePlace F) (t : ℝ) : TR.Rinf F := fun v => if v = w then Real.exp t else 1

/- English proof (translation)
Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : v = w <;> simp [eR, h, Real.exp_add]`.
-/
private theorem eR_add (w : InfinitePlace F) (s t : ℝ) : eR w (s + t) = eR w s * eR w t := by
  funext v
  by_cases h : v = w <;> simp [eR, h, Real.exp_add]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : v = w <;> simp [eR, h]`.
-/
private theorem eR_zero (w : InfinitePlace F) : eR w 0 = 1 := by
  funext v
  by_cases h : v = w <;> simp [eR, h]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Simplify `Real.hasDerivAt_exp 0` using `[eR]`. Simplify `hasDerivAt_const (0 : ℝ) (1 : ℝ)` using `[eR, h]`.
-/
private theorem hasDerivAt_eR (w : InfinitePlace F) : HasDerivAt (eR w) (Pi.single w 1 : TR.Rinf F) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using Real.hasDerivAt_exp 0
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def eU (w : InfinitePlace F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨eR w t, eR w (-t), by rw [← eR_add, add_neg_cancel, eR_zero], by rw [← eR_add, neg_add_cancel, eR_zero]⟩

/- English proof (translation)
The claim follows from `Units.ext (eR_add w s t)`.
-/
private theorem eU_add (w : InfinitePlace F) (s t : ℝ) : eU w (s + t) = eU w s * eU w t :=
  Units.ext (eR_add w s t)

private def aI (w : InfinitePlace F) (t : ℝ) : (A F)ˣ := TR.infId F (eU w t)

/- English proof (translation)
Rewrite using `[aI, eU_add, map_mul]`. Both sides reduce to the same expression.
-/
private theorem aI_add (w : InfinitePlace F) (s t : ℝ) : aI w (s + t) = aI w s * aI w t := by
  rw [aI, eU_add, map_mul]; rfl

/- English proof (translation)
Establish `h : eU w 0 = 1` using `Units.ext (eR_zero w)`. Rewrite using `[aI, h, map_one]`.
-/
private theorem aI_zero (w : InfinitePlace F) : aI w 0 = 1 := by
  have h : eU w 0 = 1 := Units.ext (eR_zero w)
  rw [aI, h, map_one]

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← aI_add, neg_add_cancel, aI_zero])`.
-/
private theorem aI_neg (w : InfinitePlace F) (t : ℝ) : aI w (-t) = (aI w t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← aI_add, neg_add_cancel, aI_zero])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `1 - TR.sInf F 1 + TR.sInf F (eR w t) = _`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.
-/
private theorem aI_val (w : InfinitePlace F) (t : ℝ) :
    ((aI w t : (A F)ˣ) : A F) = 1 + TR.sInf F (eR w t - 1) := by
  change 1 - TR.sInf F 1 + TR.sInf F (eR w t) = _
  rw [map_sub]; abel

/- English proof (translation)
The claim follows from `(TR.infEq F).symm_apply_apply x`.
-/
private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x := (TR.infEq F).symm_apply_apply x

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

/- English proof (translation)
Use `TR.ad_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, pInf_sInf, pInf_sInf]`. Rewrite using `[map_mul, pFin_sInf, pFin_sInf, zero_mul]`.
-/
private theorem sInf_mul (x : TR.Rinf F) (a : A F) : TR.sInf F x * a = TR.sInf F (x * TR.pInf F a) := by
  refine TR.ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

/- English proof (translation)
Rewrite using `[aI_val, map_add, pInf_sInf, map_one]`. Normalize the expressions using the abelian group laws.
-/
private theorem pInf_aI (w : InfinitePlace F) (t : ℝ) : TR.pInf F (aI w t : (A F)ˣ) = eR w t := by
  rw [aI_val, map_add, pInf_sInf, map_one]; abel

/- English proof (translation)
Rewrite using `[aI_val, map_add, pFin_sInf, map_one, add_zero]`.
-/
private theorem pFin_aI (w : InfinitePlace F) (t : ℝ) : pFin F (aI w t : (A F)ˣ) = 1 := by
  rw [aI_val, map_add, pFin_sInf, map_one, add_zero]

/- English proof (translation)
Establish `h1 : ((aI w t : (A F)ˣ) : A F).1 = TR.infEq F (eR w t)`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) - TR.infEq F 1 + TR.infEq F (eR w t) = _`. Rewrite using `[map_one, sub_self, zero_add]`. Establish `h2 : ((aI w t : (A F)ˣ) : A F).2 = 1`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`.

Rewrite using `[sub_zero, add_zero]`. Establish `h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1` using `finprod_eq_one_of_forall_eq_one fun v => by exact norm_one`. Establish `h4 : ∀ v : InfinitePlace F, ‖(TR.infEq F (eR w t)) v‖ = |eR w t v|` using `fun v => by`. Establish `h` using `(InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.dist_eq (eR w t v) 0`. Establish `h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 0 : v.Completion) = 0` using `map_zero _`.

Rewrite using `[← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]`. Conclude with `h`. Unfold `ab`. Rewrite using `[IdeleGroup.ideleModule_eq, h1, h2, h3, mul_one]`. Rewrite using `[Finset.prod_eq_single w]`.

Rewrite using `[(IsTotallyReal.isReal w).mult_eq_one, pow_one, h4]`. Simplify using `[eR, abs_of_pos (Real.exp_pos t)]`. Introduce `v _ hv`. Rewrite using `[(IsTotallyReal.isReal v).mult_eq_one, pow_one, h4]`. Simplify using `[eR, hv]`.

Simplify using the standard rewrite rules.
-/
private theorem ab_aI (w : InfinitePlace F) (t : ℝ) : ab (aI w t) = Real.exp t := by
  have h1 : ((aI w t : (A F)ˣ) : A F).1 = TR.infEq F (eR w t) := by
    change (1 : InfiniteAdeleRing F) - TR.infEq F 1 + TR.infEq F (eR w t) = _
    rw [map_one, sub_self, zero_add]
  have h2 : ((aI w t : (A F)ˣ) : A F).2 = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  have h4 : ∀ v : InfinitePlace F, ‖(TR.infEq F (eR w t)) v‖ = |eR w t v| := fun v => by
    have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.dist_eq (eR w t v) 0
    have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 0 : v.Completion) = 0 :=
      map_zero _
    rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
    exact h
  unfold ab
  rw [IdeleGroup.ideleModule_eq, h1, h2, h3, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one, h4]
    simp [eR, abs_of_pos (Real.exp_pos t)]
  · intro v _ hv
    rw [(IsTotallyReal.isReal v).mult_eq_one, pow_one, h4]
    simp [eR, hv]
  · simp

/- English proof (translation)
Establish `e : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ`. Simplify using `[Fo.Ops.h, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, two_smul, two_mul]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `((∑ i, O.x w i (O.d w i φ) : S4 F)).1 v + 2 * φ.1 v = _`. Use `congr 1`.

Establish `: ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 = ∑ i, (O.x w i (O.d w i φ)).1` using `AddSubmonoidClass.coe_finset_sum _ _`. Rewrite using `[this, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => O.x_apply w i _ v`.
-/
private theorem h_apply (O : Fo.Ops F) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    (O.h w φ).1 v = (∑ i, Fo.cw w (v i) * (O.d w i φ).1 v) + 2 * φ.1 v := by
  have e : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ := by
    simp [Fo.Ops.h, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, two_smul, two_mul]
  rw [e]
  change ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 v + 2 * φ.1 v = _
  congr 1
  have : ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 = ∑ i, (O.x w i (O.d w i φ)).1 :=
    AddSubmonoidClass.coe_finset_sum _ _
  rw [this, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => O.x_apply w i _ v

/- English proof (translation)
Set `x : ℝ → Fin 4 → TR.Rinf F` to `fun r i => (eR w r - 1) * TR.pInf F (v i)`. Set `x' : Fin 4 → TR.Rinf F` to `fun i => (Pi.single w 1 : TR.Rinf F) * TR.pInf F (v i)`. Establish `hx0 : x 0 = 0` using `by funext i; simp [x, eR_zero]`. Establish `hx : HasDerivAt x x' 0`. Use `hasDerivAt_pi.2 fun i => ?_` and prove the remaining obligations.

Conclude with `((hasDerivAt_eR w).sub_const 1).mul_const _`. Establish `h1` using `hS φ v x x' hx0 hx`. Establish `h2 : (fun r : ℝ => φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) = fun r => φ.1 fun i => v i + TR.sInf F (x r i)`. Use function extensionality and compare the values at `r`. Use `congrArg φ.1 (funext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[aI_val, add_mul, one_mul, sInf_mul]`. Rewrite `h1` using `[← h2]`. Establish `h3 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ)) (2 : ℂ) 0`. Establish `h : HasDerivAt (fun r : ℝ => Real.exp (2 * r)) 2 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp`.

Simplify using `using h.ofReal_comp`. Establish `h4 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) _ 0` using `h3.mul h1`. Use `h4.congr_deriv ?_` and prove the remaining obligations. Establish `h5 : (∑ i, ∑ u, ((x' i u : ℝ) : ℂ) * (O.d u i φ).1 v) = ∑ i, Fo.cw w (v i) * (O.d w i φ).1 v`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single w]`. Simplify using `[x', Fo.cw]`. Introduce `u _ hu`. Simplify using `[x', hu]`. Simplify using the standard rewrite rules.

Rewrite using `[h5, h_apply, aI_zero]`. Simplify using `[add_comm]`.
-/
private theorem key (O : Fo.Ops F) (hS : SDiff O) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i)
      ((O.h w φ).1 v) 0 := by
  let x : ℝ → Fin 4 → TR.Rinf F := fun r i => (eR w r - 1) * TR.pInf F (v i)
  let x' : Fin 4 → TR.Rinf F := fun i => (Pi.single w 1 : TR.Rinf F) * TR.pInf F (v i)
  have hx0 : x 0 = 0 := by funext i; simp [x, eR_zero]
  have hx : HasDerivAt x x' 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    exact ((hasDerivAt_eR w).sub_const 1).mul_const _
  have h1 := hS φ v x x' hx0 hx
  have h2 : (fun r : ℝ => φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) =
      fun r => φ.1 fun i => v i + TR.sInf F (x r i) := by
    funext r
    refine congrArg φ.1 (funext fun i => ?_)
    rw [aI_val, add_mul, one_mul, sInf_mul]
  rw [← h2] at h1
  have h3 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ)) (2 : ℂ) 0 := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (2 * r)) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp
    simpa using h.ofReal_comp
  have h4 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) _ 0 :=
    h3.mul h1
  refine h4.congr_deriv ?_
  have h5 : (∑ i, ∑ u, ((x' i u : ℝ) : ℂ) * (O.d u i φ).1 v) = ∑ i, Fo.cw w (v i) * (O.d w i φ).1 v := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single w]
    · simp [x', Fo.cw]
    · intro u _ hu
      simp [x', hu]
    · simp
  rw [h5, h_apply, aI_zero]
  simp [add_comm]

/- English proof (translation)
Rewrite using `[← eR_add, add_neg_cancel, eR_zero]`.
-/
private theorem eR_mul_neg (w : InfinitePlace F) (t : ℝ) : eR w t * eR w (-t) = 1 := by
  rw [← eR_add, add_neg_cancel, eR_zero]

/- English proof (translation)
Rewrite using `[← eR_add, neg_add_cancel, eR_zero]`.
-/
private theorem eR_neg_mul (w : InfinitePlace F) (t : ℝ) : eR w (-t) * eR w t = 1 := by
  rw [← eR_add, neg_add_cancel, eR_zero]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Simplify `(hasDerivAt_neg (0 : ℝ)).exp` using `[eR]`. Simplify `hasDerivAt_const (0 : ℝ) (1 : ℝ)` using `[eR, h]`.
-/
private theorem hasDerivAt_eR_neg (w : InfinitePlace F) :
    HasDerivAt (fun t => eR w (-t)) (-(Pi.single w 1 : TR.Rinf F)) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using (hasDerivAt_neg (0 : ℝ)).exp
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def cT (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![eR w t, 0; 0, eR w (-t)], !![eR w (-t), 0; 0, eR w t],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul]⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `!![eR w (s + t), 0; 0, eR w (-(s + t))] = !![eR w s, 0; 0, eR w (-s)] * !![eR w t, 0; 0, eR w (-t)]`. Rewrite using `[Matrix.mul_fin_two, neg_add, eR_add, eR_add]`. Simplify using the standard rewrite rules.
-/
private theorem cT_add (w : InfinitePlace F) (s t : ℝ) : cT w (s + t) = cT w s * cT w t := by
  refine Units.ext ?_
  change !![eR w (s + t), 0; 0, eR w (-(s + t))] = !![eR w s, 0; 0, eR w (-s)] * !![eR w t, 0; 0, eR w (-t)]
  rw [Matrix.mul_fin_two, neg_add, eR_add, eR_add]
  simp

/- English proof (translation)
Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `hasDerivAt_eR w` using `[cT]`. Simplify `hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)` using `[cT]`. Simplify `hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)` using `[cT]`.

Simplify `hasDerivAt_eR_neg w` using `[cT]`.
-/
private theorem hasDerivAt_cT (w : InfinitePlace F) : HasDerivAt (fun t => TR.toL (cT w t).val)
    (TR.toL (Matrix.single 0 0 (Pi.single w 1)) - TR.toL (Matrix.single 1 1 (Pi.single w 1))) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [cT] using hasDerivAt_eR w
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_eR_neg w

/- English proof (translation)
Establish `hn : ((aI w t)⁻¹ : (A F)ˣ) = aI w (-t)` using `(aI_neg w t).symm`. Use `TR.ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TR.pInf_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Conclude with `pInf_aI w t`. Conclude with `map_zero (TR.pInf F)`. Conclude with `map_zero (TR.pInf F)`. Express the relevant statement in the definitionally equal form `TR.pInf F (((aI w t)⁻¹ : (A F)ˣ) : A F) = eR w (-t)`. Rewrite using `[hn]`.

Conclude with `pInf_aI w (-t)`. Rewrite using `[TR.pFin_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `pFin_aI w t`.

Conclude with `map_zero (pFin F)`. Conclude with `map_zero (pFin F)`. Express the relevant statement in the definitionally equal form `pFin F (((aI w t)⁻¹ : (A F)ˣ) : A F) = 1`. Rewrite using `[hn]`. Conclude with `pFin_aI w (-t)`.
-/
private theorem gl_mD_aI (w : InfinitePlace F) (t : ℝ) : gl (mD (aI w t)) = TR.infGL F 2 (cT w t) := by
  have hn : ((aI w t)⁻¹ : (A F)ˣ) = aI w (-t) := (aI_neg w t).symm
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pInf_aI w t
    · exact map_zero (TR.pInf F)
    · exact map_zero (TR.pInf F)
    · change TR.pInf F (((aI w t)⁻¹ : (A F)ˣ) : A F) = eR w (-t)
      rw [hn]; exact pInf_aI w (-t)
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pFin_aI w t
    · exact map_zero (pFin F)
    · exact map_zero (pFin F)
    · change pFin F (((aI w t)⁻¹ : (A F)ˣ) : A F) = 1
      rw [hn]; exact pFin_aI w (-t)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E] {D : Dat F E}

/- English proof (translation)
Establish `hη : W.η.1 (aI w t) = 1`. Establish `h : aI w t = aI w (t / 2) ^ 2`. Rewrite using `[pow_two, ← aI_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, map_pow]`. Conclude with `W.η_sq _`. Establish `he : Real.exp t ^ 2 = Real.exp (2 * t)`. Rewrite using `[pow_two, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[W.Om_m, hη, ab_aI, he]`. Simplify using the standard rewrite rules.
-/
private theorem om_aI (W : Weil D) (w : InfinitePlace F) (t : ℝ) (φ : S4 F) (v : V4 F) :
    (W.Om (mD (aI w t)) φ).1 v =
      ((Real.exp (2 * t) : ℝ) : ℂ) * φ.1 fun i => ((aI w t : (A F)ˣ) : A F) * v i := by
  have hη : W.η.1 (aI w t) = 1 := by
    have h : aI w t = aI w (t / 2) ^ 2 := by
      rw [pow_two, ← aI_add]
      congr 1
      ring
    rw [h, map_pow]
    exact W.η_sq _
  have he : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [W.Om_m, hη, ab_aI, he]
  simp

end UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

end

open UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves in
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D O W w`. Establish `hS` using `sDiff F O`. Use `⟨fun t => mD (aI w t), cT w, ⟨cT_add w, hasDerivAt_cT w⟩, gl_mD_aI w, fun φ t v => ?_⟩` and prove the remaining obligations. Establish `hk` using `key O hS w φ (fun i => ((aI w t : (A F)ˣ) : A F) * v i)`. Establish `hk' : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i)) ((O.h w φ).1 fun i => ((aI w t : (A F)ˣ) : A F) * v i) (t - t)`.

Rewrite using `[sub_self]` and apply the resulting hypothesis. Establish `h` using `(hk'.comp_sub_const t t).const_mul ((Real.exp (2 * t) : ℝ) : ℂ)`. Establish `e : (fun s => (W.Om (mD (aI w s)) φ).1 v) = fun s => ((Real.exp (2 * t) : ℝ) : ℂ) * (((Real.exp (2 * (s - t)) : ℝ) : ℂ) * φ.1 fun i => ((aI w (s - t) : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i))`. Use function extensionality and compare the values at `s`. Rewrite using `[om_aI W w s φ v, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]`.

Establish `h1 : 2 * t + 2 * (s - t) = 2 * s` using `by ring`. Rewrite using `[h1]`. Use `congrArg _ (congrArg φ.1 (funext fun i => ?_))` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← Units.val_mul, ← aI_add, sub_add_cancel]`. Express the relevant statement in the definitionally equal form `HasDerivAt (fun s => (W.Om (mD (aI w s)) φ).1 v) ((W.Om (mD (aI w t)) (O.h w φ)).1 v) t`.

Rewrite using `[e, om_aI W w t (O.h w φ) v]`. Conclude with `h`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.curveH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveH O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  have hS := sDiff F O
  refine ⟨fun t => mD (aI w t), cT w, ⟨cT_add w, hasDerivAt_cT w⟩, gl_mD_aI w, fun φ t v => ?_⟩
  have hk := key O hS w φ (fun i => ((aI w t : (A F)ˣ) : A F) * v i)
  have hk' : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) *
      φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i))
      ((O.h w φ).1 fun i => ((aI w t : (A F)ˣ) : A F) * v i) (t - t) := by
    rwa [sub_self]
  have h := (hk'.comp_sub_const t t).const_mul ((Real.exp (2 * t) : ℝ) : ℂ)
  have e : (fun s => (W.Om (mD (aI w s)) φ).1 v) = fun s => ((Real.exp (2 * t) : ℝ) : ℂ) *
      (((Real.exp (2 * (s - t)) : ℝ) : ℂ) *
        φ.1 fun i => ((aI w (s - t) : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i)) := by
    funext s
    rw [om_aI W w s φ v, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have h1 : 2 * t + 2 * (s - t) = 2 * s := by ring
    rw [h1]
    refine congrArg _ (congrArg φ.1 (funext fun i => ?_))
    rw [← mul_assoc, ← Units.val_mul, ← aI_add, sub_add_cancel]
  change HasDerivAt (fun s => (W.Om (mD (aI w s)) φ).1 v) ((W.Om (mD (aI w t)) (O.h w φ)).1 v) t
  rw [e, om_aI W w t (O.h w φ) v]
  exact h
