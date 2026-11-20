import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

/- English proof (translation)
Introduce `hc E _ _ _ n f hf hb α`. Take `⟨C, hC⟩` from `hb`. Take `⟨h1, h2⟩` from `hc E n f hf`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Establish `hch : ∀ g x, ‖chart f g x‖ ≤ C`.

Introduce `g x`. Unfold `GlobalTheory.CuspRep.chart`. Use `split_ifs`. Conclude with `hC _`. Simplify using `using hC0`.

Establish `hbd : ∀ g x, ‖chart f g x * α x‖ ≤ C * ‖α x‖`. Introduce `g x`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hch g x) (norm_nonneg _)`. Use `haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance`.

Use `haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `hint : Integrable (fun x => C * ‖α x‖)` using `(α.integrable.norm).const_mul C`. Use `haveI : FirstCountableTopology (GA E n) := GroundTheory.Automorphic.FourierWhittaker.firstCountableTopology_adelicGL ..`. Use `⟨?_, ∫ x, C * ‖α x‖, fun g => ?_⟩` and prove the remaining obligations.

Unfold `conv`. Use `continuous_of_dominated (bound := fun x => C * ‖α x‖) (fun g => ?_) (fun g => ?_) hint ?_` and prove the remaining obligations. Conclude with `((h2 g).mul α.continuous.measurable).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall (hbd g)`. Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations.

Use `Continuous.mul ?_ continuous_const` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ invSet E n`. Conclude with `h1.comp_continuous (f := fun g : GA E n => (g, x)) (by fun_prop) fun g => ⟨Set.mem_univ _, hx⟩`. Establish `: (fun g => chart f g x) = fun _ => 0`. Use function extensionality and compare the values at `g`.

Unfold `GlobalTheory.CuspRep.chart`. Conclude with `dif_neg hx`. Rewrite using `[this]`. Conclude with `continuous_const`. Conclude with `norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (hbd g))`.
-/
theorem UpperTheory.V.Af.StrongMultiplicityOne.convCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont := by
  intro hc E _ _ _ n f hf hb α
  obtain ⟨C, hC⟩ := hb
  obtain ⟨h1, h2⟩ := hc E n f hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hch : ∀ g x, ‖chart f g x‖ ≤ C := by
    intro g x
    unfold GlobalTheory.CuspRep.chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hbd : ∀ g x, ‖chart f g x * α x‖ ≤ C * ‖α x‖ := by
    intro g x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hch g x) (norm_nonneg _)
  haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun x => C * ‖α x‖) := (α.integrable.norm).const_mul C
  haveI : FirstCountableTopology (GA E n) :=
    GroundTheory.Automorphic.FourierWhittaker.firstCountableTopology_adelicGL ..
  refine ⟨?_, ∫ x, C * ‖α x‖, fun g => ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun x => C * ‖α x‖) (fun g => ?_) (fun g => ?_) hint ?_
    · exact ((h2 g).mul α.continuous.measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hbd g)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Continuous.mul ?_ continuous_const
      by_cases hx : x ∈ invSet E n
      · exact h1.comp_continuous (f := fun g : GA E n => (g, x)) (by fun_prop) fun g => ⟨Set.mem_univ _, hx⟩
      · have : (fun g => chart f g x) = fun _ => 0 := by
          funext g
          unfold GlobalTheory.CuspRep.chart
          exact dif_neg hx
        rw [this]
        exact continuous_const
  · exact norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (hbd g))
