import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.HasDerivAtShift

open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}

/- English proof (translation)
The claim follows from `continuous_id`.
-/
lemma cont_of : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) := continuous_id

/- English proof (translation)
Conclude with `MeasureTheory.mem_ae_iff.mpr hconc`.
-/
lemma ae_mem (hconc : μ Gᶜ = 0) : ∀ᵐ x ∂μ, (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) ∈ G := by
  exact MeasureTheory.mem_ae_iff.mpr hconc

/- English proof (translation)
Establish `hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}` using `hGc.preimage cont_of`. Establish `h1 : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}` using `hφ.comp cont_of.continuousOn (fun x hx => hx)`. Establish `h2` using `h1.aestronglyMeasurable (μ := μ) hcl.measurableSet`. Rewrite `h2` using `[Measure.restrict_eq_self_of_ae_mem (s := {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}) (ae_mem hconc)]`. Then use the resulting hypothesis.
-/
lemma aesm_of_contOn (hGc : IsClosed G) (hconc : μ Gᶜ = 0) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) : AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  have hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} := hGc.preimage cont_of
  have h1 : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx)
  have h2 := h1.aestronglyMeasurable (μ := μ) hcl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}) (ae_mem hconc)] at h2

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩`. Establish `hSc : IsCompact {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G}` using `hK.inter_right hGc`. Establish `hcont : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G}` using `hφ.comp cont_of.continuousOn (fun x hx => hx.2)`. Establish `hI` using `hcont.integrableOn_compact (μ := μ) hSc`. Establish `hInd` using `(integrable_indicator_iff hSc.isClosed.measurableSet).mpr hI`.

Use `hInd.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_mem hconc] with x hx`. Distinguish the cases in `hxK : (Matrix.of x) ∈ K`. Conclude with `Set.indicator_of_mem (show x ∈ {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} from ⟨hxK, hx⟩) _`. Rewrite using `[Set.indicator_of_notMem (fun h => hxK h.1), hz _ hx hxK]`.
-/
lemma integrable_of_contOn (hGc : IsClosed G) (hconc : μ Gᶜ = 0)
    (hfin : ∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hz : ∀ g ∈ G, g ∉ K → φ g = 0) : Integrable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  have hSc : IsCompact {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} := hK.inter_right hGc
  have hcont : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx.2)
  have hI := hcont.integrableOn_compact (μ := μ) hSc
  have hInd := (integrable_indicator_iff hSc.isClosed.measurableSet).mpr hI
  refine hInd.congr ?_
  filter_upwards [ae_mem hconc] with x hx
  by_cases hxK : (Matrix.of x) ∈ K
  · exact Set.indicator_of_mem (show x ∈ {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} from ⟨hxK, hx⟩) _
  · rw [Set.indicator_of_notMem (fun h => hxK h.1), hz _ hx hxK]

end QnRdSkewW
