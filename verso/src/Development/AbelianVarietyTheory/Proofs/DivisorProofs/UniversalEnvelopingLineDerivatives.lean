import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DopEqSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.WordAlg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adjoin_word : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), ∃ z : List (ℝ → GAd σ J) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f : SmG σ J, dop z f.1 = (u f).1 := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD u hu
  classical
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    obtain ⟨γ₁, γ₂, e1, e2, e3⟩ := exists_lines h hJ τ X
    generalize (1 / 2 : ℂ) • (X - adj (J.map τ.1) X) = X₁ at e1 e3
    generalize (-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X) = X₂ at e2 e3
    have hX : D X = D X₁ + Complex.I • D X₂ := by rw [← map_smul, ← map_add, ← e3]
    refine ⟨Finsupp.single [γ₁] 1 + Finsupp.single [γ₂] Complex.I, fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl <;>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl) <;>
        obtain rfl := List.mem_singleton.1 hγ
      exacts [e1.isRealLine h, e2.isRealLine h]
    · rw [dop_add_comb, dop_single, dop_single]
      rw [hX, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD.2 _ _ e1 f,
        hD.2 _ _ e2 f]
      funext g
      simp
  | algebraMap c =>
    refine ⟨Finsupp.single [] c, fun l hl γ hγ => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl)
      simp at hγ
    rw [dop_single]
    funext g
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨z + z', fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl
      exacts [hz l hl γ hγ, hz' l hl γ hγ]
    · rw [dop_add_comb, ez, ez', LinearMap.add_apply, Submodule.coe_add]
  | mul x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨wordMul z z', fun m hm γ hγ => ?_, fun f => ?_⟩
    · obtain ⟨l, hl, l', hl', rfl⟩ := mem_support_wordMul hm
      rcases List.mem_append.1 hγ with h' | h'
      exacts [hz l hl γ h', hz' l' hl' γ h']
    · obtain ⟨-, h2⟩ := GlobalTheory.UAut.DopComp.dop_dop σ J f.1 f.2 z z' hz hz'
      rw [← h2, ez', ez (y f), Module.End.mul_apply]

end GlobalTheory.LeviHC.WordAlg
