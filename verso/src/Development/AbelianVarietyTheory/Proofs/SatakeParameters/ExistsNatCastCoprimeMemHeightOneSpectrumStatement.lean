import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatCastCoprimeMemHeightOneSpectrum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.natCast_mem_heightOneSpectrum_coprime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsNatCastCoprimeMemHeightOneSpectrum.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_natCast_coprime_mem_heightOneSpectrum : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  first | exact @GlobalTheory.natCast_mem_heightOneSpectrum_coprime | exact GlobalTheory.natCast_mem_heightOneSpectrum_coprime | (intros; apply GlobalTheory.natCast_mem_heightOneSpectrum_coprime <;> assumption)
