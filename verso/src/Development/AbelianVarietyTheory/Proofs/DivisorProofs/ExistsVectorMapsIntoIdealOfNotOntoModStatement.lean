import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowFilt.IsOpp.exists_ker_vec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsVectorMapsIntoIdealOfNotOntoMod.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_ker_vec | exact GlobalTheory.LowFilt.IsOpp.exists_ker_vec | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_ker_vec <;> assumption)
