import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `continuous_of_continuousAt_zero (i : k →+* k').toAddMonoidHom ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Express the relevant statement in the definitionally equal form `Filter.Tendsto i (nhds 0) (nhds 0)`. Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero' k').tendsto_right_iff]`. Introduce `r hr`.

Take `⟨c, rfl⟩` from `valuation_surjective r`. Establish `hc : valuation k (i.symm c) ≠ 0`. Introduce `h0`. Establish `h2` using `(h (i.symm c) 0).2 (by simp [h0])`. Simplify using `only [RingEquiv.apply_symm_apply, map_zero, le_zero_iff] at h2`.

Conclude with `hr h2`. Establish `hm : {x : k | valuation k x < valuation k (i.symm c)} ∈ nhds (0 : k)` using `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨_, hc, subset_rfl⟩`. Use `filter_upwards [hm] with a ha`. Establish `h3` using `h (i.symm c) a`. Rewrite `h3` using `[RingEquiv.apply_symm_apply]`.

Conclude with `not_le.1 fun h4 => absurd (h3.1 h4) (not_le.2 ha)`.
-/
private theorem continuous_of_val_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (h : ∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) :
    Continuous i := by
  refine continuous_of_continuousAt_zero (i : k →+* k').toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  change Filter.Tendsto i (nhds 0) (nhds 0)
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k').tendsto_right_iff]
  intro r hr
  obtain ⟨c, rfl⟩ := valuation_surjective r
  have hc : valuation k (i.symm c) ≠ 0 := by
    intro h0
    have h2 := (h (i.symm c) 0).2 (by simp [h0])
    simp only [RingEquiv.apply_symm_apply, map_zero, le_zero_iff] at h2
    exact hr h2
  have hm : {x : k | valuation k x < valuation k (i.symm c)} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨_, hc, subset_rfl⟩
  filter_upwards [hm] with a ha
  have h3 := h (i.symm c) a
  rw [RingEquiv.apply_symm_apply] at h3
  exact not_le.1 fun h4 => absurd (h3.1 h4) (not_le.2 ha)

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ i hi z a`. Establish `h1` using `(isoVal k k' i hi).1`. Establish `hc : Continuous i` using `continuous_of_val_iff i h1`. Establish `hc' : Continuous i.symm` using `continuous_of_val_iff i.symm fun a b => by`. Use `h1 (i.symm a) (i.symm b)` as an intermediate fact.

Simplify `this.symm` using `only [RingEquiv.apply_symm_apply]`. Establish `hn` using `GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hc hc' a`. Use `ext`. Rewrite using `[val_absPow, val_absPow]`. Conclude with `congrArg (fun t : ℝ => (t : ℂ) ^ z) hn`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.isoAbs :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a := by
  intro k k' _ _ _ _ _ _ _ _ i hi z a
  have h1 := (isoVal k k' i hi).1
  have hc : Continuous i := continuous_of_val_iff i h1
  have hc' : Continuous i.symm := continuous_of_val_iff i.symm fun a b => by
    have := h1 (i.symm a) (i.symm b)
    simpa only [RingEquiv.apply_symm_apply] using this.symm
  have hn := GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hc hc' a
  ext
  rw [val_absPow, val_absPow]
  exact congrArg (fun t : ℝ => (t : ℂ) ^ z) hn
