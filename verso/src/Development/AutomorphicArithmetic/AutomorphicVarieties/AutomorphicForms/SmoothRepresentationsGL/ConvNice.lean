import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `hc hf E _ _ _ n f hN α`. Take `⟨h1, h2⟩` from `hc E n f hN.cont hN.bdd α`. Use `⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `γ g`. Establish `e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g`.

Use function extensionality and compare the values at `x`. Simplify using `only [chart, mul_assoc, hN.left γ]`. Simplify using `only [conv, e]`. Introduce `r hr hrn g haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by`. Take `⟨C, hC, hDC⟩` from `exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)`.

Conclude with `⟨by`. Rewrite using `[Measure.restrict_apply_univ]`. Conclude with `(measure_mono hDC).trans_lt hC.measure_lt_top⟩`. Establish `h` using `hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g`. Simplify using `only [mul_one] at h`.

Establish `e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0`. Use function extensionality and compare the values at `fun g' => hN.cusp r hr hrn g'`. Rewrite using `[constantTerm, h, e]`. Simplify using `[conv, chart]`. Take `⟨V, hV⟩` from `hN.level`.

Use `⟨V, fun g v hv => ?_⟩` and prove the remaining obligations. Establish `e : (fun x => f (x * finGL E n v)) = f` using `funext fun x => hV x v hv`. Rewrite using `[conv, ← TR.chart_rt_fin, e, conv]`. Use function extensionality and compare the values at `g haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) := ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩`. Conclude with `hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuou …`.
-/
theorem UpperTheory.V.Af.Smo.convNice :
    UpperTheory.V.Af.Smo.ConvCont → UpperTheory.V.Af.Smo.ConvFub → UpperTheory.V.Af.Smo.ConvNice := by
  intro hc hf E _ _ _ n f hN α
  obtain ⟨h1, h2⟩ := hc E n f hN.cont hN.bdd α
  refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g := by
      funext x
      simp only [chart, mul_assoc, hN.left γ]
    simp only [conv, e]
  · intro r hr hrn g
    haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by
      obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
      exact ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
    have h := hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r))
      unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g
    simp only [mul_one] at h
    have e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0 :=
      funext fun g' => hN.cusp r hr hrn g'
    rw [constantTerm, h, e]
    simp [conv, chart]
  · obtain ⟨V, hV⟩ := hN.level
    refine ⟨V, fun g v hv => ?_⟩
    have e : (fun x => f (x * finGL E n v)) = f := funext fun x => hV x v hv
    rw [conv, ← TR.chart_rt_fin, e, conv]
  · funext g
    haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) :=
      ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    exact hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL
      (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuous_uGL
      (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp
        (FourierWhittaker.continuous_supSum 0).neg)) ⟨1, fun _ => (Circle.norm_coe _).le⟩ g
