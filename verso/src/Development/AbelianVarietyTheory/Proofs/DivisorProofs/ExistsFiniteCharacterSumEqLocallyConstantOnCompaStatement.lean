import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCharacterSumEqLocallyConstantOnCompa
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteCharacterSumEqLocallyConstantOnCompa.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ → ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  first | exact @GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | exact GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | (intros; apply GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact <;> assumption)
