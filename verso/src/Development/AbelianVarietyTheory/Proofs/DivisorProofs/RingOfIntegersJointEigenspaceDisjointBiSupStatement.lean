import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingOfIntegersJointEigenspaceDisjointBiSup.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  first | exact @GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | exact GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | (intros; apply GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup <;> assumption)
