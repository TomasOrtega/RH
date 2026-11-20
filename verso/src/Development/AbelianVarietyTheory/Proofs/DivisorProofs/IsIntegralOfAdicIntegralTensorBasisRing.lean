import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isIntegral_of_isIntB : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  intro v C _ _ _ κ b h1 hmul y hy
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) b with he
  have hsmul : ∀ (a : v.adicCompletionIntegers ℚ) (x : v.adicCompletion ℚ ⊗[ℚ] C),
      a • x = (a : v.adicCompletion ℚ) • x := fun a x => (algebraMap_smul (v.adicCompletion ℚ) a x).symm
  have hadd : ∀ x z, IsIntB v b x → IsIntB v b z → IsIntB v b (x + z) := fun x z hx hz i => by
    rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hz i)
  let S : Subalgebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] C) :=
    { carrier := {x | IsIntB v b x}
      mul_mem' := fun {x z} hx hz => hmul x z hx hz
      one_mem' := h1
      add_mem' := fun {x z} hx hz => hadd x z hx hz
      zero_mem' := isIntB_zero v b
      algebraMap_mem' := fun a => by
        show IsIntB v b (algebraMap _ _ a)
        rw [Algebra.algebraMap_eq_smul_one, hsmul]
        intro i
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact mul_mem a.2 (h1 i) }
  have hS : Subalgebra.toSubmodule S = Submodule.span (v.adicCompletionIntegers ℚ)
      (Set.range fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
    apply le_antisymm
    · intro x hx
      rw [← e.sum_repr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ : ∃ c : v.adicCompletionIntegers ℚ, (c : v.adicCompletion ℚ) = e.repr x i :=
        ⟨⟨_, hx i⟩, rfl⟩
      rw [← hc, ← hsmul, he, Algebra.TensorProduct.basis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact isIntB_tmul_basis v b j
  refine IsIntegral.of_mem_of_fg S ?_ y hy
  rw [hS]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.AdicSpan
