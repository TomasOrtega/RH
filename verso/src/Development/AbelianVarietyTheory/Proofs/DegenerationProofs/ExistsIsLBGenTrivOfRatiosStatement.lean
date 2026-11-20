import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsIsLBGenTrivOfRatios.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_isLB_genTriv_of_ratios' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | exact GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | (intros; apply GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios <;> assumption)
