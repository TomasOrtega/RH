import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointVertDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (liftVar pullDeg joinCoord mcIdeal IsVertDiv)

open JoinPointVerticalDivisor in

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z b f g hD`. Take `⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩` from `hD`. Use `⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(k | k)`. Simplify `hb k` using `[pullDeg]`.

Simplify using `[pullDeg]`. Rewrite using `[rename_mem_mcIdeal_iff]` and apply the resulting hypothesis. Rewrite using `[rename_mem_mcIdeal_iff]` and apply the resulting hypothesis. Introduce `Q hQ hPQ hQO`. Establish `hle : mcIdeal O x ≤ Q.comap (rename (liftVar (ι` using `ι) ι')) := fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x z h).mpr hh))`.

Establish `hO : (Q.comap (rename (liftVar (ι` using `ι) ι'))).comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by`. Rewrite `hQO`, the goal using `[eq_bot_iff]`. Introduce `c hc`. Apply `hQO` to reduce the goal to its premises. Simplify `hc` using `[Ideal.mem_comap, rename_C]`.

Take `⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩` from `hU _ (comap_isMultiProjPrime hQ) hle hO`. Use `⟨rename (liftVar ι') u, rename (liftVar ι') v, ⟨_, isMultiHomog_rename hu⟩, ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩` and prove the remaining obligations. Use `(rename_mem_mcIdeal_iff O x z _).mpr huv` as an intermediate fact. Simplify `this` using `only [map_sub, map_mul]`.
-/
theorem JoinVerticalDivisor.proof : JoinVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O x ≤ Q.comap (rename (liftVar (ι := ι) ι')) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x z h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ι'))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ι') u, rename (liftVar ι') v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x z _).mpr huv
    simpa only [map_sub, map_mul] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
