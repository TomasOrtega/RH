import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCharactersPrescribedValues.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.exists_characters_prescribed_values : ∀ (B : Base) (X : PreX B.toPre) (mu : Fin B.R.m → HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ) (eta : HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ), ∃ Ch : Chars B.fields (B.primes X) B.R.m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  first | exact @GlobalTheory.BaseChars.exists_chars | exact GlobalTheory.BaseChars.exists_chars | (intros; apply GlobalTheory.BaseChars.exists_chars <;> assumption)
