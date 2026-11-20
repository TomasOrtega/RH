import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwist
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteInvariantsOfScalarNeOneTwist.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  first | exact @GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | exact GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | (intros; apply GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one <;> assumption)
