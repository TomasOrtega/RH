import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ _ _ L _ _ _ τ _`. Establish `hcs : ContinuousSMul F L` using `IsModuleTopology.toContinuousSMul F L`. Establish `hca : ContinuousAdd L` using `IsModuleTopology.toContinuousAdd F L`. Establish `htg : IsTopologicalAddGroup L` using `{ continuous_neg := by`. Establish `: (fun x : L => -x) = fun x => (-1 : F) • x` using `by funext x; simp`.

Rewrite using `[this]`. Conclude with `continuous_const.smul continuous_id }`. Set `N : NormedAddCommGroup L` to `spectralNorm.normedAddCommGroup F L`. Set `NS : NormedSpace F L` to `spectralNorm.normedSpace F L`. Set `τ' : TopologicalSpace L` to `N.toUniformSpace.toTopologicalSpace`.

Establish `h1 : τ ≤ τ'`. Rewrite using `[← continuous_id_iff_le]`. Conclude with `@IsModuleTopology.continuous_of_linearMap F _ _ L _ _ τ _ L _ _ τ' inferInstance inferInstance LinearMap.id`. Establish `h2 : τ' ≤ τ`. Rewrite using `[← continuous_id_iff_le]`.

Conclude with `@LinearMap.continuous_of_finiteDimensional F _ L _ _ τ' inferInstance inferInstance L _ _ τ htg hcs _ inferInstance _ (LinearMap.id)`. Establish `hτ : τ = τ'` using `le_antisymm h1 h2`. Substitute `hτ` using the available equality. Establish `hU : IsUltrametricDist L` using `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))`. Establish `hPF : ProperSpace F` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`.

Establish `hPL : ProperSpace L` using `FiniteDimensional.proper F L`. Establish `hd : ∀ y : L, dist y 0 = spectralNorm F L y` using `fun y => by`. Rewrite using `[dist_zero_right]`. Both sides reduce to the same expression. Establish `hS : {y : L | spectralNorm F L y ≤ 1} = Metric.closedBall (0 : L) 1`.

Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Metric.mem_closedBall, hd]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`. Conclude with `IsUltrametricDist.isOpen_closedBall _ one_ne_zero`.

Rewrite using `[hS]`. Conclude with `isCompact_closedBall _ _`. Introduce `U hU0`. Take `⟨ε, hε, hb⟩` from `Metric.mem_nhds_iff.mp hU0`. Conclude with `⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, hd]; exact hy)⟩`.
-/
theorem spectralNorm_closedBall_isOpen_isCompact_nhds_basis : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  intro F _ _ _ _ L _ _ _ τ _
  have hcs : ContinuousSMul F L := IsModuleTopology.toContinuousSMul F L
  have hca : ContinuousAdd L := IsModuleTopology.toContinuousAdd F L
  have htg : IsTopologicalAddGroup L :=
    { continuous_neg := by
        have : (fun x : L => -x) = fun x => (-1 : F) • x := by funext x; simp
        rw [this]; exact continuous_const.smul continuous_id }
  let N : NormedAddCommGroup L := spectralNorm.normedAddCommGroup F L
  let NS : NormedSpace F L := spectralNorm.normedSpace F L
  let τ' : TopologicalSpace L := N.toUniformSpace.toTopologicalSpace
  have h1 : τ ≤ τ' := by
    rw [← continuous_id_iff_le]
    exact @IsModuleTopology.continuous_of_linearMap F _ _ L _ _ τ _ L _ _ τ' inferInstance inferInstance LinearMap.id
  have h2 : τ' ≤ τ := by
    rw [← continuous_id_iff_le]
    exact @LinearMap.continuous_of_finiteDimensional F _ L _ _ τ' inferInstance inferInstance L _ _ τ htg hcs _ inferInstance _ (LinearMap.id)
  have hτ : τ = τ' := le_antisymm h1 h2
  subst hτ
  have hU : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))
  have hPF : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hPL : ProperSpace L := FiniteDimensional.proper F L
  have hd : ∀ y : L, dist y 0 = spectralNorm F L y := fun y => by
    rw [dist_zero_right]; rfl
  have hS : {y : L | spectralNorm F L y ≤ 1} = Metric.closedBall (0 : L) 1 := by
    ext y; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  · rw [hS]; exact isCompact_closedBall _ _
  · intro U hU0
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hU0
    exact ⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, hd]; exact hy)⟩

end GlobalTheory
