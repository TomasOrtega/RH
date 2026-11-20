import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckeDoubleCosetOperatorsStandardFacts.lean&line=671#L671)
-/
theorem _root_.GlobalTheory.T.heckeDoubleCosetOperators_standardFacts : HeckeStdPlain := by
  first | exact @GlobalTheory.HeckeStdFacts.heckeStdPlain | exact GlobalTheory.HeckeStdFacts.heckeStdPlain | (intros; apply GlobalTheory.HeckeStdFacts.heckeStdPlain <;> assumption)
