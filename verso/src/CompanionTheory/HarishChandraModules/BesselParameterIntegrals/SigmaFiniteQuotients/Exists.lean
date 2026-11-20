import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SigmaFiniteQuotients.ExistsQuotientMeasureUnitaryGroup

open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace CompanionTheory.D.Upq.Quot

section Abstract

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteOnCompacts_of_sigmaFinite (η : Measure H) [SigmaFinite η] [IsMulLeftInvariant η] :
    IsFiniteMeasureOnCompacts η := by
  have K : PositiveCompacts H := Classical.arbitrary _
  have h := haarMeasure_unique η K
  have hK : η K ≠ ∞ := fun hK => by
    rw [hK] at h
    have h1 : ∀ n, haarMeasure K (spanningSets η n) = 0 := fun n => by
      by_contra hn
      have := measure_spanningSets_lt_top η n
      rw [show η (spanningSets η n) = (∞ • haarMeasure K) (spanningSets η n) by rw [← h],
        Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at this
      exact lt_irrefl _ this
    have h2 := measure_iUnion_null h1
    rw [iUnion_spanningSets, measure_univ_eq_zero] at h2
    exact NeZero.ne _ h2
  refine ⟨fun L hL => ?_⟩
  rw [h, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top hK.lt_top hL.measure_lt_top

end Abstract

open PI CompanionTheory.D.Upq.ModEx

variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_comap_toM (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G) : (μ.comap (MG.toM (hG := hG))).map MG.toM = μ := by
  rw [MG.measurableEmbedding_toM.map_comap, MG.range_toM]
  exact restrict_eq_self_of_ae_mem h0

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem comap_map_mul (hG : IsMatGroup G) {μ : Measure (MtM m)} (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G)
    (g : MG G hG) (hl : μ.map (lmulQ g.mat) = μ) :
    (μ.comap (MG.toM (hG := hG))).map (g * ·) = μ.comap MG.toM := by
  have hι := MG.measurableEmbedding_toM (hG := hG)
  apply hι.map_injective
  rw [map_map hι.measurable (measurable_const_mul g)]
  have : MG.toM ∘ (fun x : MG G hG => g * x) = lmulQ g.mat ∘ MG.toM := rfl
  rw [this, ← map_map (measurable_lmulQ _) hι.measurable, map_comap_toM hG h0, hl]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsHaarOnM.lt_top_of_isCompact (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (hμ : IsHaarOnM G μ) {K : Set (MtM m)} (hK : IsCompact K) : μ K < ∞ := by
  obtain ⟨hσ, -, h0, hl⟩ := hμ
  have hι := MG.measurableEmbedding_toM (hG := hG)
  have hmap := map_comap_toM hG h0
  haveI : T2Space (MG G hG) := MG.isClosedEmbedding_mat.isEmbedding.t2Space
  haveI : SigmaFinite (μ.comap (MG.toM (hG := hG))) :=
    SigmaFinite.of_map _ hι.measurable.aemeasurable (by rwa [hmap])
  haveI : IsMulLeftInvariant (μ.comap (MG.toM (hG := hG))) :=
    ⟨fun g => comap_map_mul hG h0 g (hl _ g.mem)⟩
  haveI := finiteOnCompacts_of_sigmaFinite (μ.comap (MG.toM (hG := hG)))
  rw [← hmap, hι.map_apply]
  exact ((MG.isClosedEmbedding_mat (hG := hG)).isCompact_preimage hK).measure_lt_top

end CompanionTheory.D.Upq.Quot

end
