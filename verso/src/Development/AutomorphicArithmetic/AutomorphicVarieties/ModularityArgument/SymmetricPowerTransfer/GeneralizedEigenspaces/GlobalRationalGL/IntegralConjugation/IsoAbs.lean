import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
