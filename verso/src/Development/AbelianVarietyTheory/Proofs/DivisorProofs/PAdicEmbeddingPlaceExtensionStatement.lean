import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingPlaceExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrueGeo.ExtOfEmb.exists_ext` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPAdicEmbeddingPlaceExtension.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.p_adic_embedding_place_extension : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : AlgebraicClosure F →+* ℂ_[p]), ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v), (p : 𝓞 F) ∈ v.asIdeal ∧ ∀ a, ‖ι a‖ ≤ 1 ↔ a ∈ e.O := by
  first | exact @GlobalTheory.TrueGeo.ExtOfEmb.exists_ext | exact GlobalTheory.TrueGeo.ExtOfEmb.exists_ext | (intros; apply GlobalTheory.TrueGeo.ExtOfEmb.exists_ext <;> assumption)
