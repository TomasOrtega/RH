import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsLocFrac
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

/- English proof (translation)
Establish `key : ∀ s, ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0 → P ≤ W`. Introduce `s hs`. Assume the negation of the conclusion as `hPW`. Apply `hs` to reduce the goal to its premises. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨hmin, -⟩`. Conclude with `hPW (le_trans le_sup_left hmin.1.2)`. Rewrite `hW` using `[Finsupp.mem_support_iff]`. Simplify using `only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at hW`.

Distinguish the cases in `hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0`. Distinguish the cases in `hg : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W = 0`. Simplify using `[hf, hg] at hW`. Conclude with `key g hg`. Conclude with `key f hf`.
-/
theorem le_of_mem_ratCyc_support {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    (hW : W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support) : P ≤ W := by
  have key : ∀ s, ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0 → P ≤ W := by
    intro s hs
    by_contra hPW
    apply hs
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    exact hPW (le_trans le_sup_left hmin.1.2)
  rw [Finsupp.mem_support_iff] at hW
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0
  · by_cases hg : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W = 0
    · simp [hf, hg] at hW
    · exact key g hg
  · exact key f hf

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B hM fl₁ fl₂ I hI G hG n Y R b f g hD`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval`. Use `Finsupp.sum_congr fun W hW => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hV` using `hFib O K ι _ d hM b f g hD W hW`.

Establish `: (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).IsPrime` using `hV.1.1`. Take `⟨hmc, B', -, hfl⟩` from `hRes O Ω K ι x d N V B hM (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) hV.1 (Ideal.map_mono (le_of_mem_ratCyc_support hW))`. Take `⟨fl₁', h₁, -⟩` from `hfl fl₁`. Take `⟨fl₂', h₂, -⟩` from `hfl fl₂`. Establish `hV' : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdea …`.

Rewrite using `[hmc]`. Conclude with `hV`. Use `SegreFlagIndep.segreFlagIndep_homogeneous_implies_general _ _ ι (hSeg (IsLocalRing.ResidueField O) _ K ι) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W)) d hV' N _ B' fl₁' fl₂' I hI G hG n Y R` as an intermediate fact. Rewrite `this` using `[hmc, h₁, h₂]`. Conclude with `this`.
-/
theorem FullFlagVerticalSymmetric.proof (hFib : VerticalDivisorFibreVariety.Statement)
    (hRes : FullFlagRestriction.Statement)
    (hSeg : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
      (ι : K → Type) [∀ k, Fintype (ι k)], IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι) :
    FullFlagVerticalSymmetric.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B hM fl₁ fl₂ I hI G hG n Y R b f g hD
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  congr 1
  have hV := hFib O K ι _ d hM b f g hD W hW
  have : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).IsPrime := hV.1.1
  obtain ⟨hmc, B', -, hfl⟩ := hRes O Ω K ι x d N V B hM (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) hV.1
    (Ideal.map_mono (le_of_mem_ratCyc_support hW))
  obtain ⟨fl₁', h₁, -⟩ := hfl fl₁
  obtain ⟨fl₂', h₂, -⟩ := hfl fl₂
  have hV' : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W))) d := by
    rw [hmc]
    exact hV
  have := SegreFlagIndep.segreFlagIndep_homogeneous_implies_general _ _ ι (hSeg (IsLocalRing.ResidueField O) _ K ι)
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W)) d hV' N _ B' fl₁' fl₂' I hI G hG n Y R
  rw [hmc, h₁, h₂] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
