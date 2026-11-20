import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassSplit

noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Covol

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

def phiMap (x : mixedSpace K) : ι → ℂ := fun i => if cj i then (starRingEnd ℂ) (x.2 (σ i)) else x.2 (σ i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : cj i <;> simp [phiMap, h]`.
-/
theorem phiMap_add (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by
  funext i
  by_cases h : cj i <;> simp [phiMap, h]

/- English proof (translation)
Establish `hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1` using `by first`. Consider the case `(rw [volume_pi, Measure.pi_of_empty]; simp)`. Consider the case `(rw [volume_pi, Measure.pi_univ]; simp)`. Consider the case `simp [volume_pi, Measure.pi_univ]`. Consider the case `(erw [Measure.pi_univ]; simp)`.

Establish `h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ)) volume volume`. Use `⟨measurable_snd, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.volume_eq_prod, Measure.map_snd_prod]`. Use `first`. Consider the case `rw [hu, one_smul]`.

Consider the case `simp only [hu, one_smul]`. Consider the case `(convert one_smul ENNReal (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ)); exact hu)`. Establish `h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i)) volume volume` using `MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)`. Establish `hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume`. Use `Complex.conjLIE.measurePreserving` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | (funext z; simp) | (ext z; simp)`. Establish `h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i) (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ))`. Use `measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ)) (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)` and prove the remaining obligations. Distinguish the cases in `h : cj i`.

Use `first`. Consider the case `(simp only [if_pos h]; exact hc)`. Consider the case `simpa [h] using hc`. Use `first`. Consider the case `(simp only [if_neg h]; exact MeasurePreserving.id _)`.

Consider the case `simp [h, MeasurePreserving.id]`. Use `first`. Consider the case `exact h3.comp (h2.comp h1)`. Consider the case `(rw [volume_pi]; exact h3.comp (h2.comp h1))`.
-/
theorem phiMap_mp [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by
  have hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    first
    | (rw [volume_pi, Measure.pi_of_empty]; simp)
    | (rw [volume_pi, Measure.pi_univ]; simp)
    | simp [volume_pi, Measure.pi_univ]
    | (erw [Measure.pi_univ]; simp)
  have h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    first
    | rw [hu, one_smul]
    | simp only [hu, one_smul]
    | (convert one_smul ENNReal (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ)); exact hu)
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i))
      volume volume :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
    have := Complex.conjLIE.measurePreserving
    convert this using 2
    all_goals first | rfl | (funext z; simp) | (ext z; simp)
  have h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i)
      (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ)) := by
    refine measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
      (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)
    by_cases h : cj i
    · first
      | (simp only [if_pos h]; exact hc)
      | simpa [h] using hc
    · first
      | (simp only [if_neg h]; exact MeasurePreserving.id _)
      | simp [h, MeasurePreserving.id]
  first
  | exact h3.comp (h2.comp h1)
  | (rw [volume_pi]; exact h3.comp (h2.comp h1))

end Covol

end Formalism.L2.SG.NGCut.SplitEmbedding
