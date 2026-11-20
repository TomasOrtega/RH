import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ComplexMetric

/- English proof (translation)
Introduce `A _ N ρ`. Rewrite using `[continuous_iff_isClosed]`. Introduce `Z hZ`. Set `Z' : Set (ProjectiveSpectrum (ProjSpace.grading A N))` to `Z`. Establish `hZ' : IsClosed Z'` using `hZ`.

Establish `e : Z' = ProjectiveSpectrum.zeroLocus _ (ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A))`. Rewrite using `[ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ'.closure_eq]`. Establish `hpre : (projPoint ρ : CP N → projectiveSpace A N) ⁻¹' Z = ⋂ d, ⋂ f ∈ {f | f ∈ ProjSpace.grading A N d ∧ f ∈ ProjectiveSpectrum.vanishingIdeal Z'}, {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal}`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]`.

Express the relevant statement in the definitionally equal form `projPoint ρ v ∈ Z' ↔ _`. Use `conv_lhs => rw [e]`. Express the relevant statement in the definitionally equal form `(ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A)) ⊆ (projPoint ρ v).asHomogeneousIdeal ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h d f _ hf`.

Conclude with `h hf`. Introduce `h`. Conclude with `ProjScheme.le_of_homogeneous _ _ h`. Rewrite using `[hpre]`. Conclude with `isClosed_iInter fun d => isClosed_biInter fun f hf => isClosed_setOf_mem_projPoint ρ hf.1`.
-/
theorem ProjPointContinuous.proof : ProjPointContinuous.Statement.{u} := by
  intro A _ N ρ
  rw [continuous_iff_isClosed]
  intro Z hZ
  let Z' : Set (ProjectiveSpectrum (ProjSpace.grading A N)) := Z
  have hZ' : IsClosed Z' := hZ
  have e : Z' = ProjectiveSpectrum.zeroLocus _
      (ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A)) := by
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ'.closure_eq]
  have hpre : (projPoint ρ : CP N → projectiveSpace A N) ⁻¹' Z =
      ⋂ d, ⋂ f ∈ {f | f ∈ ProjSpace.grading A N d ∧ f ∈ ProjectiveSpectrum.vanishingIdeal Z'},
        {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]
    change projPoint ρ v ∈ Z' ↔ _
    conv_lhs => rw [e]
    change (ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A)) ⊆
      (projPoint ρ v).asHomogeneousIdeal ↔ _
    constructor
    · intro h d f _ hf
      exact h hf
    · intro h
      exact ProjScheme.le_of_homogeneous _ _ h
  rw [hpre]
  exact isClosed_iInter fun d => isClosed_biInter fun f hf => isClosed_setOf_mem_projPoint ρ hf.1

end ComplexMetric

end GroundTheory.Heights₂.Heights
