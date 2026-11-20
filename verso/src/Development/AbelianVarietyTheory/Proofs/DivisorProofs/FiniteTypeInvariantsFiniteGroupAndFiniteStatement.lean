import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFinite
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteType_invariants_and_finite` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteTypeInvariantsFiniteGroupAndFinite.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.finiteType_invariants_finite_group_and_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by
  first | exact @GlobalTheory.finiteType_invariants_and_finite | exact GlobalTheory.finiteType_invariants_and_finite | (intros; apply GlobalTheory.finiteType_invariants_and_finite <;> assumption)
