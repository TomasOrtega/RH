import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.length_quotient_smul_sup_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLengthQuotientSmulSupLeIntermediate.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
