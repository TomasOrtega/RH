import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `O _ _ _ _ h2 ι _ wt J hJ`. Use `haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι`. Take `⟨τ, hττ, hev, hw⟩` from `ep_ps O h2 ι wt`. Establish `hτJ : ∀ y ∈ J, τ y ∈ J`. Introduce `y hy`.

Establish `e` using `hw 1 y`. Establish `hs : sg (MvPowerSeries ι O) 1 = -1`. Simplify using `only [sg]`. Rewrite using `[show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]`. Rewrite `e` using `[hs]`.

Establish `: τ y = y - 2 * wcomp O wt 1 y` using `by linear_combination e`. Rewrite using `[this]`. Conclude with `J.sub_mem hy (J.mul_mem_left 2 (hJ y hy 1))`. Establish `hτm : ∀ y ∈ maximalIdeal (MvPowerSeries ι O), τ y ∈ maximalIdeal (MvPowerSeries ι O)`. Introduce `y hy`.

Rewrite `hy`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Apply `hy` to reduce the goal to its premises. Rewrite using `[← hττ y]`. Conclude with `hu.map τ`.

Establish `hτN : ∀ y ∈ maximalIdeal (MvPowerSeries ι O) * J, τ y ∈ maximalIdeal (MvPowerSeries ι O) * J`. Introduce `y hy`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `m hm j hj`. Rewrite using `[map_mul]`.

Conclude with `Ideal.mul_mem_mul (hτm m hm) (hτJ j hj)`. Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ ha hb`. Take `⟨a, g, z, hz, hle, hmin⟩` from `ep_basis O h2 (MvPowerSeries ι O) τ hττ J (maximalIdeal (MvPowerSeries ι O) * J) hτJ hτN le_rfl`.

Use `⟨Fin a ⊕ Fin g, inferInstance, z, Space.Loc.par a g, ?_, ?_, hmin⟩` and prove the remaining obligations. Introduce `s`. Rewrite using `[← hev]`. Conclude with `(hz s).2`. Apply `le_antisymm` to reduce the goal to its premises.

Apply `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J) (maximalIdeal_le_jacobson _)` to reduce the goal to its premises. Conclude with `hle`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `(hz s).1`.
-/
theorem UpperTheory.V.Fr.ep_rels :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2) (J : Ideal (MvPowerSeries ι O)), IsHomog O wt J → ∃ (κ : Type) (_ : Fintype κ) (f : κ → MvPowerSeries ι O) (wf : κ → ZMod 2), (∀ u, f u ∈ wtPart O wt (wf u)) ∧ J = Ideal.span (Set.range f) ∧ ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries ι O) * J → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 ι _ wt J hJ
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  obtain ⟨τ, hττ, hev, hw⟩ := ep_ps O h2 ι wt
  have hτJ : ∀ y ∈ J, τ y ∈ J := by
    intro y hy
    have e := hw 1 y
    have hs : sg (MvPowerSeries ι O) 1 = -1 := by
      simp only [sg]
      rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    rw [hs] at e
    have : τ y = y - 2 * wcomp O wt 1 y := by linear_combination e
    rw [this]
    exact J.sub_mem hy (J.mul_mem_left 2 (hJ y hy 1))
  have hτm : ∀ y ∈ maximalIdeal (MvPowerSeries ι O), τ y ∈ maximalIdeal (MvPowerSeries ι O) := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    rw [← hττ y]
    exact hu.map τ
  have hτN : ∀ y ∈ maximalIdeal (MvPowerSeries ι O) * J,
      τ y ∈ maximalIdeal (MvPowerSeries ι O) * J := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm j hj
      rw [map_mul]
      exact Ideal.mul_mem_mul (hτm m hm) (hτJ j hj)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb
  obtain ⟨a, g, z, hz, hle, hmin⟩ :=
    ep_basis O h2 (MvPowerSeries ι O) τ hττ J (maximalIdeal (MvPowerSeries ι O) * J) hτJ hτN le_rfl
  refine ⟨Fin a ⊕ Fin g, inferInstance, z, Space.Loc.par a g, ?_, ?_, hmin⟩
  · intro s
    rw [← hev]
    exact (hz s).2
  · apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J)
        (maximalIdeal_le_jacobson _)
      exact hle
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact (hz s).1
