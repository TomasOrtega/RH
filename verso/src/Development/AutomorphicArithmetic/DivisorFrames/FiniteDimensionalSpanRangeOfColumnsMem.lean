import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.LocalEmbeddings.ULieDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

open scoped TensorProduct NNReal Matrix ComplexConjugate ContDiff
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.GLTwoHecke GlobalTheory.StdPar GlobalTheory.ULie
open GlobalTheory.Doubling (absE ideleAtInf)
open GlobalTheory.UAut (IsMaxCpt)

/- English proof (translation)
Introduce `A B Φ S hS hcol`. Set `F : Module.Dual ℂ S →ₗ[ℂ] (B → ℂ)` to `{ toFun := fun f b => f ⟨fun a => Φ a b, hcol b⟩ map_add' := fun f g => rfl map_smul' := fun c f => rfl }`. Establish `hle : Submodule.span ℂ (Set.range Φ) ≤ LinearMap.range F`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Use `⟨(LinearMap.proj (R := ℂ) (φ := fun _ : A => ℂ) a).comp S.subtype, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem UpperTheory.finiteDimensional_span_range_of_columns_mem :
    ∀ (A B : Type) (Φ : A → B → ℂ) (S : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ S → (∀ b, (fun a => Φ a b) ∈ S) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range Φ)) := by
  intro A B Φ S hS hcol
  let F : Module.Dual ℂ S →ₗ[ℂ] (B → ℂ) :=
    { toFun := fun f b => f ⟨fun a => Φ a b, hcol b⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hle : Submodule.span ℂ (Set.range Φ) ≤ LinearMap.range F := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : A => ℂ) a).comp S.subtype, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle
