import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TensIsoExt.tensIso_of_exact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLatticeTwistExactSequenceCohomology.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.lattice_twist_exact_sequence_cohomology : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  first | exact @GlobalTheory.TensIsoExt.tensIso_of_exact | exact GlobalTheory.TensIsoExt.tensIso_of_exact | (intros; apply GlobalTheory.TensIsoExt.tensIso_of_exact <;> assumption)
