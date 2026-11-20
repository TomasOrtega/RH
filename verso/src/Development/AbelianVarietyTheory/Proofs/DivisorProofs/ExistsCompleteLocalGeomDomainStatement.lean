import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomain
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCompleteLocalGeomDomain.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exists_complete_local_geomDomain' : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  first | exact @GlobalTheory.SepRing.exists_complete_local_geomDomain | exact GlobalTheory.SepRing.exists_complete_local_geomDomain | (intros; apply GlobalTheory.SepRing.exists_complete_local_geomDomain <;> assumption)
