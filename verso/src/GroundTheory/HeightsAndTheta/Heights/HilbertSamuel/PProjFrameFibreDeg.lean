import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

/- English proof (translation)
Introduce `D Ω _ _ κ _ x e hP hF G i hi`. Take `⟨hc, hcoord, hrel, hrange⟩` from `hRel D Ω κ x e hP hF G`. Establish `: CharZero G.Φ'` using `charZero_of_inj_zero hc`. Establish `hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0` using `fun k h => hi k (by`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]`.

Conclude with `h)`. Establish `hch` using `Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz (hPt D Ω κ x e hP hF G).1.2.1`. Set `k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)` to `⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩`. Set `u : Ix κ → G.Φ'` to `fun p => G.x' ⟨Sum.inl p.1, p.2⟩`. Establish `hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩`.

Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩`. Conclude with `⟨⟨(), j⟩, rfl⟩`. Conclude with `absurd ⟨t, rfl⟩ h`.

Introduce and unpack `⟨⟨_, j⟩, rfl⟩`. Conclude with `⟨⟨k₀, j⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `ptDeg (RingHom.ker _) i = _`. Rewrite using `[hch, hset]`. Rewrite using `[hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀) (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel (hTr D Ω κ x e hP hF G) hrange]`.

Conclude with `hRat (Ix κ) G.Φ' Ω u x D e hcoord`.
-/
theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
