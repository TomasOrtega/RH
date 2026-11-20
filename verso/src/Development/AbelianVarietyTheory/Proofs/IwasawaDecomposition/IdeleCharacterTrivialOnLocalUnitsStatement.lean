import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIdeleCharacterTrivialOnLocalUnits.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.idele_character_trivial_on_local_units : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  first | exact @GlobalTheory.Mem.LocTriv.eq_one_of_local | exact GlobalTheory.Mem.LocTriv.eq_one_of_local | (intros; apply GlobalTheory.Mem.LocTriv.eq_one_of_local <;> assumption)
