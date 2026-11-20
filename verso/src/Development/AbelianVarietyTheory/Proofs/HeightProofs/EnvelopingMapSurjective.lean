import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

/- English proof (translation)
Establish `hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L))` using `fun u => Quotient.exists_rep u`. Take `⟨t, rfl⟩` from `hs u`. Proceed by induction on `t using TensorAlgebra.induction with`. Consider the case `algebraMap r`. Rewrite using `[AlgHom.commutes, Algebra.algebraMap_eq_smul_one]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)`. Consider the case `ι x`. Express the relevant statement in the definitionally equal form `UniversalEnvelopingAlgebra.ι ℂ x ∈ _`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `tmul z X`. Establish `h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `mul a b ha hb`. Rewrite using `[map_mul]`.

Establish `h` using `Submodule.mul_mem_mul ha hb`. Rewrite `h` using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩`. Conclude with `⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩`.

Consider the case `add a b ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`.
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
Introduce `D V τ u`. Conclude with `(Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)`.
-/
theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
