import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Treat this case separately. A detailed English derivation is pending.
-/
theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
