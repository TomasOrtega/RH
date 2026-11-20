import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTateTwistReductionCohomologyMapUnique.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.tateTwistReduction_cohomology_map_unique : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) → ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  first
  | exact @GlobalTheory.EtC.RedUniq.op_eq
  | exact GlobalTheory.EtC.RedUniq.op_eq
  | (intros; apply GlobalTheory.EtC.RedUniq.op_eq <;> assumption)
