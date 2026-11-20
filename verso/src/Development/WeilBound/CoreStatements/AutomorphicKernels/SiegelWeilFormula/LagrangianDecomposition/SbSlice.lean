import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.KillsLinearMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinPart
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInv

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `ι : (κ' → W) →L[ℝ] (κ' ⊕ κ'' → W)` to `ContinuousLinearMap.pi fun j => Sum.elim (fun i => ContinuousLinearMap.proj i) (fun _ => 0) j`. Apply the tactic sequence `have hι : ∀ v, ι v = Sum.elim v 0 := fun v => by funext j; rcases j with j | j <;> rfl`. Establish `hn : ∀ v, ‖v‖ ≤ ‖ι v‖` using `fun v => by`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Use `norm_le_pi_norm (ι v) (Sum.inl i)` as an intermediate fact.

Rewrite `this`, the goal using `[hι]`. Simplify using `using this`. Use `⟨SchwartzMap.compCLM ℂ (g := ι) ι.hasTemperateGrowth ⟨1, 1, fun v => ?_⟩ f, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, pow_one]`. Combine the linear relations using `[hn v]`.

Simplify using `[hι]`.
-/
theorem exists_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {κ' κ'' : Type} [Fintype κ'] [Fintype κ'']
    (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) :
    ∃ f' : SchwartzMap (κ' → W) ℂ, ∀ v, f' v = f (Sum.elim v 0) := by
  let ι : (κ' → W) →L[ℝ] (κ' ⊕ κ'' → W) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun i => ContinuousLinearMap.proj i) (fun _ => 0) j
  have hι : ∀ v, ι v = Sum.elim v 0 := fun v => by funext j; rcases j with j | j <;> rfl
  have hn : ∀ v, ‖v‖ ≤ ‖ι v‖ := fun v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (ι v) (Sum.inl i)
    rw [hι] at this ⊢
    simpa using this
  refine ⟨SchwartzMap.compCLM ℂ (g := ι) ι.hasTemperateGrowth ⟨1, 1, fun v => ?_⟩ f, fun v => ?_⟩
  · rw [one_mul, pow_one]; linarith [hn v]
  · simp [hι]

/- English proof (translation)
Establish `hc : Continuous fun z : κ' → X => (Sum.elim z 0 : κ' ⊕ κ'' → X)`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Break down `j with j | j` into its components or cases. Conclude with `continuous_apply j`. Conclude with `continuous_const`.

Use `⟨hg.1.comp_continuous hc, ?_⟩` and prove the remaining obligations. Establish `hK : IsCompact ((fun x : κ' ⊕ κ'' → X => x ∘ Sum.inl) '' tsupport g)` using `hg.2.isCompact.image (continuous_pi fun i => continuous_apply _)`. Use `HasCompactSupport.intro' hK hK.isClosed fun z hz => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hz` to reduce the goal to its premises.

Conclude with `⟨Sum.elim z 0, subset_tsupport _ hne, rfl⟩`.
-/
theorem sb_slice {X : Type} [TopologicalSpace X] [Zero X] [T2Space X] {κ' κ'' : Type}
    {g : (κ' ⊕ κ'' → X) → ℂ} (hg : g ∈ SB (κ' ⊕ κ'' → X)) : (fun z : κ' → X => g (Sum.elim z 0)) ∈ SB (κ' → X) := by
  have hc : Continuous fun z : κ' → X => (Sum.elim z 0 : κ' ⊕ κ'' → X) := by
    refine continuous_pi fun j => ?_
    rcases j with j | j
    · exact continuous_apply j
    · exact continuous_const
  refine ⟨hg.1.comp_continuous hc, ?_⟩
  have hK : IsCompact ((fun x : κ' ⊕ κ'' → X => x ∘ Sum.inl) '' tsupport g) :=
    hg.2.isCompact.image (continuous_pi fun i => continuous_apply _)
  refine HasCompactSupport.intro' hK hK.isClosed fun z hz => ?_
  by_contra hne
  apply hz
  exact ⟨Sum.elim z 0, subset_tsupport _ hne, rfl⟩

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
