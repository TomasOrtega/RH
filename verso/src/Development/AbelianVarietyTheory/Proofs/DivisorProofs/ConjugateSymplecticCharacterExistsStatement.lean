import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjugateSymplecticCharacterExists.lean&line=249#L249)
-/
theorem _root_.GlobalTheory.T.conjugate_symplectic_character_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ η : Formalism.L2.Host.HChar E, η.IsUnitary ∧ (CG.ofChar η).IsCsd ∧ ∀ τ : E →+* ℂ, ∃ k : ℤ, expo η τ = (k : ℂ) + 1 / 2 := by
  first | exact @GlobalTheory.HalfCsd.exists_unitary_csd_half | exact GlobalTheory.HalfCsd.exists_unitary_csd_half | (intros; apply GlobalTheory.HalfCsd.exists_unitary_csd_half <;> assumption)
