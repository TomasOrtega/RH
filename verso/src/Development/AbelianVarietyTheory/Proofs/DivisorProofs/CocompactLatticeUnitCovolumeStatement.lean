import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCocompactLatticeUnitCovolume.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.cocompact_lattice_unit_covolume : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ : Γ, γ • g ∈ K) → ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | exact GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | (intros; apply GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one <;> assumption)
