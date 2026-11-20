import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMuCharacter.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.mu_character : MuChar := by
  first | exact @GlobalTheory.MuCharProof.muChar_holds | exact GlobalTheory.MuCharProof.muChar_holds | (intros; apply GlobalTheory.MuCharProof.muChar_holds <;> assumption)
