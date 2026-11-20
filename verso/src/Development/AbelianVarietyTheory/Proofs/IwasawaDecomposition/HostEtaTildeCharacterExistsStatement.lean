import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.EtaT.etaT_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHostEtaTildeCharacterExists.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
