import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sInf F : Rinf F → Ad F)` using `(TR.continuous_infEq F).prodMk continuous_const`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
private theorem cc_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨hu, ?_⟩` and prove the remaining obligations. Establish `e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹` using `funext fun x => Matrix.coe_units_inv _`. Rewrite using `[e]`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hd : IsUnit ((u x).val).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit`.

Take `⟨d, hd⟩` from `hd`. Use `ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt` and prove the remaining obligations. Rewrite using `[← hd]`. Conclude with `NormedRing.inverse_continuousAt d`.
-/
private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Rinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

/- English proof (translation)
Introduce `E _ _ _ n f hf`. Establish `h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n)`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Set `u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Rinf E)` to `fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit`. Establish `hu : Continuous u` using `cc_unit E n u (continuous_snd.comp continuous_subtype_val)`.

Establish `e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) = fun z => f (z.1.1 * infGL E n (u z))`. Use function extensionality and compare the values at `z`. Establish `h : IsUnit (Matrix.of z.1.2)` using `z.2.2`. Express the relevant statement in the definitionally equal form `chart f z.1.1 z.1.2 = _`. Rewrite using `[chart, dif_pos h]`.

Rewrite using `[e]`. Conclude with `hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))`. Use `⟨h1, fun g => ?_⟩` and prove the remaining obligations. Establish `h2 : ContinuousOn (chart f g) (invSet E n)` using `h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn fun x hx => ⟨Set.mem_univ _, hx⟩`. Establish `h3` using `h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const TR.isOpen_invSet.measurableSet`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ invSet E n`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hx]`. Rewrite using `[Set.piecewise_eq_of_notMem _ _ _ hx, chart, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]`.
-/
theorem UpperTheory.V.Af.Smo.chartCont :
    UpperTheory.V.Af.Smo.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Rinf E) :=
      fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit
    have hu : Continuous u := cc_unit E n u (continuous_snd.comp continuous_subtype_val)
    have e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) =
        fun z => f (z.1.1 * infGL E n (u z)) := by
      funext z
      have h : IsUnit (Matrix.of z.1.2) := z.2.2
      change chart f z.1.1 z.1.2 = _
      rw [chart, dif_pos h]
    rw [e]
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))
  refine ⟨h1, fun g => ?_⟩
  classical
  have h2 : ContinuousOn (chart f g) (invSet E n) :=
    h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn
      fun x hx => ⟨Set.mem_univ _, hx⟩
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const TR.isOpen_invSet.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ invSet E n
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, chart, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]
