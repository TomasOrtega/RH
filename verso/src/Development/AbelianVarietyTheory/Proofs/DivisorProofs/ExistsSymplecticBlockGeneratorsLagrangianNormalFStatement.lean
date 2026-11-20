import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSymplecticBlockGeneratorsLagrangianNormalF.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L = Fintype.card κ →
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  first | exact @GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | exact GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | (intros; apply GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure <;> assumption)
