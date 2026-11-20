import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]`. Conclude with `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x j).1 (y j).1`.
-/
private theorem infPartPi_add' {F : Type} [Field F] [NumberField F] (x y : V4 F) :
    infPartPi (x + y) = infPartPi x + infPartPi y := by
  funext j
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x j).1 (y j).1

/- English proof (translation)
Simplify using `only [at1, Pi.single_add, map_add]`.
-/
private theorem placeEmbedReal_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (s t : ℝ) :
    at1 w (s + t) = at1 w s + at1 w t := by
  simp only [at1, Pi.single_add, map_add]

/- English proof (translation)
Establish `h : Continuous fun t : ℝ => (Pi.single w t : TR.Rinf F)`. Use `continuous_pi fun u => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Simplify using `only [Pi.single_eq_same]`.

Conclude with `continuous_id`. Simplify `continuous_const` using `[Pi.single_eq_of_ne hu]`. Conclude with `((TR.continuous_infEq F).comp h).prodMk continuous_const`.
-/
private theorem continuous_placeEmbedReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    Continuous (at1 w : ℝ → A F) := by
  have h : Continuous fun t : ℝ => (Pi.single w t : TR.Rinf F) := by
    refine continuous_pi fun u => ?_
    by_cases hu : u = w
    · subst hu; simp only [Pi.single_eq_same]; exact continuous_id
    · simpa [Pi.single_eq_of_ne hu] using continuous_const
  exact ((TR.continuous_infEq F).comp h).prodMk continuous_const

/- English proof (translation)
Set `L : ℝ →+ (Fin 4 → mixedEmbedding.mixedSpace F)` to `{ toFun := fun t => infPartPi (Pi.single i (at1 w t) : V4 F) map_zero' := by`. Establish `h0 : at1 w (0 : ℝ) = (0 : A F)` using `by simp [at1]`. Rewrite using `[h0, Pi.single_zero]`. Use function extensionality and compare the values at `j`. Simplify using `only [infPartPi, Pi.zero_apply, homeomorphMixedSpace_apply]`.

Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Use the proof step `map_add' := fun s t => by`. Rewrite using `[placeEmbedReal_add, Pi.single_add, infPartPi_add'] }`. Establish `hL : Continuous L`. Use `continuous_infPartPi.comp (continuous_pi fun j => ?_)` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using continuous_placeEmbedReal w`. Simplify `continuous_const` using `[Pi.single_eq_of_ne hj]`. Establish `h` using `map_real_smul L hL t (1 : ℝ)`.

Rewrite using `[infPartPi_add']`. Establish `e : t • (1 : ℝ) = t` using `by simp`. Rewrite `h` using `[e]`. Conclude with `congrArg (infPartPi v + ·) h`.
-/
private theorem inf_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) :
    infPartPi (v + Pi.single i (at1 w t)) = infPartPi v + t • infPartPi (Pi.single i (at1 w 1) : V4 F) := by
  let L : ℝ →+ (Fin 4 → mixedEmbedding.mixedSpace F) :=
    { toFun := fun t => infPartPi (Pi.single i (at1 w t) : V4 F)
      map_zero' := by
        have h0 : at1 w (0 : ℝ) = (0 : A F) := by simp [at1]
        rw [h0, Pi.single_zero]
        funext j
        simp only [infPartPi, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun s t => by
        rw [placeEmbedReal_add, Pi.single_add, infPartPi_add'] }
  have hL : Continuous L := by
    refine continuous_infPartPi.comp (continuous_pi fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using continuous_placeEmbedReal w
    · simpa [Pi.single_eq_of_ne hj] using continuous_const
  have h := map_real_smul L hL t (1 : ℝ)
  rw [infPartPi_add']
  have e : t • (1 : ℝ) = t := by simp
  rw [e] at h
  exact congrArg (infPartPi v + ·) h

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [finPartPi, Pi.add_apply, Pi.single_eq_same]`. Express the relevant statement in the definitionally equal form `(v j).2 + 0 = (v j).2`.

Conclude with `add_zero _`. Simplify using `[finPartPi, Pi.single_eq_of_ne hj]`.
-/
private theorem fin_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) : finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + 0 = (v j).2
    exact add_zero _
  · simp [finPartPi, Pi.single_eq_of_ne hj]

/- English proof (translation)
Introduce `F _ _ _ w i φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨f, g, hg, rfl⟩` from `hG`. Use `set e := infPartPi (Pi.single i (at1 w 1) : V4 F) with he`.

Use `⟨schwartzBruhatTensorPi (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) e f) g, schwartzBruhatTensorPi_mem _ hg, fun v => ?_⟩` and prove the remaining obligations. Establish `hfun : (fun t : ℝ => schwartzBruhatTensorPi f g (v + Pi.single i (at1 w t))) = fun t : ℝ => f (infPartPi v + t • e) * g (finPartPi v)`. Use function extensionality and compare the values at `t`. Simplify using `only [schwartzBruhatTensorPi, inf_line, fin_line, he]`. Rewrite using `[hfun]`.

Establish `hline : HasDerivAt (fun t : ℝ => infPartPi v + t • e) e 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (infPartPi v)`. Establish `hf : HasFDerivAt (f : (Fin 4 → mixedEmbedding.mixedSpace F) → ℂ) (fderiv ℝ f (infPartPi v)) (infPartPi v + (0 : ℝ) • e)`. Rewrite using `[zero_smul, add_zero]`. Conclude with `(f.differentiableAt).hasFDerivAt`.

Establish `hc` using `(hf.comp_hasDerivAt (0 : ℝ) hline).mul_const (g (finPartPi v))`. Simplify `hc` using `[schwartzBruhatTensorPi, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]`. Consider the case `zero`. Conclude with `⟨0, Submodule.zero_mem _, fun v => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩`. Consider the case `add G H _ _ hG hH`.

Take `⟨a, ha, ha'⟩` from `hG`. Take `⟨b, hb, hb'⟩` from `hH`. Conclude with `⟨a + b, Submodule.add_mem _ ha hb, fun v => (ha' v).add (hb' v)⟩`. Consider the case `smul c G _ hG`. Take `⟨a, ha, ha'⟩` from `hG`.

Conclude with `⟨c • a, Submodule.smul_mem _ c ha, fun v => (ha' v).const_mul c⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.dEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi F (Fin 4) →
    ∃ φ' ∈ schwartzBruhatPi F (Fin 4), ∀ v, HasDerivAt (fun t : ℝ => φ (v + Pi.single i (at1 w t))) (φ' v) 0 := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    set e := infPartPi (Pi.single i (at1 w 1) : V4 F) with he
    refine ⟨schwartzBruhatTensorPi (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) e f) g,
      schwartzBruhatTensorPi_mem _ hg, fun v => ?_⟩
    have hfun : (fun t : ℝ => schwartzBruhatTensorPi f g (v + Pi.single i (at1 w t))) =
        fun t : ℝ => f (infPartPi v + t • e) * g (finPartPi v) := by
      funext t
      simp only [schwartzBruhatTensorPi, inf_line, fin_line, he]
    rw [hfun]
    have hline : HasDerivAt (fun t : ℝ => infPartPi v + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (infPartPi v)
    have hf : HasFDerivAt (f : (Fin 4 → mixedEmbedding.mixedSpace F) → ℂ) (fderiv ℝ f (infPartPi v))
        (infPartPi v + (0 : ℝ) • e) :=
      by
        rw [zero_smul, add_zero]
        exact (f.differentiableAt).hasFDerivAt
    have hc := (hf.comp_hasDerivAt (0 : ℝ) hline).mul_const (g (finPartPi v))
    simpa [schwartzBruhatTensorPi, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hc
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun v => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add G H _ _ hG hH =>
    obtain ⟨a, ha, ha'⟩ := hG
    obtain ⟨b, hb, hb'⟩ := hH
    exact ⟨a + b, Submodule.add_mem _ ha hb, fun v => (ha' v).add (hb' v)⟩
  | smul c G _ hG =>
    obtain ⟨a, ha, ha'⟩ := hG
    exact ⟨c • a, Submodule.smul_mem _ c ha, fun v => (ha' v).const_mul c⟩
