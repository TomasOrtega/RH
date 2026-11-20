import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.ParabolicCoord

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ _ _ _ q hq`. Use `haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaFinite μQ := inferInstance`.

Use `haveI : SFinite ((μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)).prod μQ) := inferInstance`. Establish `hΦ : Measurable (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1)`. Establish `h1 : Measurable (fun p : K × (T × Q) => (p.2.2 : G))` using `continuous_subtype_val.measurable.comp (measurable_snd.snd)`. Establish `h2 : Measurable (fun p : K × (T × Q) => m p.2.1)` using `hm.continuous.measurable.comp (measurable_snd.fst)`. Establish `h3 : Measurable (fun p : K × (T × Q) => κ p.1)` using `hκ.measurable.comp measurable_fst`.

Conclude with `(h1.mul h2.inv).mul h3`. Use `set q' : Q := ⟨q, hq⟩`. Establish `hL : Measurable (fun x : G => q * x)` using `measurable_const_mul q`. Establish `hLQ : Measurable (fun x : Q => q' * x)` using `measurable_const_mul q'`. Unfold `coordMeasure`.

Rewrite using `[Measure.map_map hL hΦ]`. Establish `hcomp : (fun x : G => q * x) ∘ (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) = (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) ∘ Prod.map id (Prod.map id (fun x : Q => q' * x))`. Use function extensionality and compare the values at `p`. Simplify using `[q', mul_assoc]`. Rewrite using `[hcomp, ← Measure.map_map hΦ (measurable_id.prodMap (measurable_id.prodMap hLQ))]`.

Use `congr 1`. Rewrite using `[← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hLQ), Measure.map_id, ← Measure.map_prod_map _ _ measurable_id hLQ, Measure.map_id, map_mul_left_eq_self]`.
-/
theorem coordMeasure_map_mul_left : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ q ∈ Q, (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK).map (fun x => q * x) = GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ _ _ _ q hq
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μQ := inferInstance
  haveI : SFinite ((μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)).prod μQ) := inferInstance
  have hΦ : Measurable (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) := by
    have h1 : Measurable (fun p : K × (T × Q) => (p.2.2 : G)) :=
      continuous_subtype_val.measurable.comp (measurable_snd.snd)
    have h2 : Measurable (fun p : K × (T × Q) => m p.2.1) :=
      hm.continuous.measurable.comp (measurable_snd.fst)
    have h3 : Measurable (fun p : K × (T × Q) => κ p.1) := hκ.measurable.comp measurable_fst
    exact (h1.mul h2.inv).mul h3
  set q' : Q := ⟨q, hq⟩
  have hL : Measurable (fun x : G => q * x) := measurable_const_mul q
  have hLQ : Measurable (fun x : Q => q' * x) := measurable_const_mul q'
  unfold coordMeasure
  rw [Measure.map_map hL hΦ]
  have hcomp : (fun x : G => q * x) ∘ (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1)
      = (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) ∘ Prod.map id (Prod.map id (fun x : Q => q' * x)) := by
    funext p
    simp [q', mul_assoc]
  rw [hcomp, ← Measure.map_map hΦ (measurable_id.prodMap (measurable_id.prodMap hLQ))]
  congr 1
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hLQ), Measure.map_id,
    ← Measure.map_prod_map _ _ measurable_id hLQ, Measure.map_id, map_mul_left_eq_self]

end GlobalTheory.ParabolicCoord
