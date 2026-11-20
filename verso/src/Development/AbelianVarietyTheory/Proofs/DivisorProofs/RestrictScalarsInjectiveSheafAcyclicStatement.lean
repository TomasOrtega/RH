import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.restr_injective_acyclic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictScalarsInjectiveSheafAcyclic.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.restrictScalars_injective_sheaf_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  first
  | exact @GlobalTheory.EtC.restr_injective_acyclic
  | exact GlobalTheory.EtC.restr_injective_acyclic
  | (intros; apply GlobalTheory.EtC.restr_injective_acyclic <;> assumption)
