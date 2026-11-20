import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin

noncomputable section

namespace PI.VolStabS.InvariantStabilizerAssembly

open PI.VolStabS MeasureTheory Measure Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.VolFromSW
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Take `⟨μ, hμ⟩` from `hSWa1.1`. Establish `: μ.IsHaarMeasure` using `hμ`. Establish `: SigmaCompactSpace (HA (AF F) σ J)` using `um_sigmaCompact_HA F E σ M J hSWa1`.

Establish `: IsMulRightInvariant μ` using `unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ`. Establish `hcl` using `us_isClosed_stab F E σ M a J X0`. Establish `: LocallyCompactSpace (stabT (AF F) σ J X0)` using `hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SigmaCompactSpace (stabT (AF F) σ J X0)` using `hcl.sigmaCompactSpace`. Take `⟨lam, μ0, hμ0, hC, -⟩` from `hLam F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ`.

Set `s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J` to `fun y => if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1`. Establish `hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F` using `F) (AF F) X0 = y) → s y • ratTup (F := F) (AF F) X0 = y := by`. Introduce `y h`. Simplify using `only [s, dif_pos h]`. Conclude with `h.choose_spec`.

Establish `: IsMulRightInvariant μ0` using `us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ0 lam s (fun f hf => hC.2 f hf s hs)`. Establish `hc : μ'' = haarScalarFactor μ'' μ0 • μ0` using `um_eq_smul_of_sigmaCompact μ'' μ0`. Establish `: IsMulRightInvariant μ''`. Use `⟨fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Measure.map_smul, map_mul_right_eq_self]`.

Conclude with `us_invInv μ''`.
-/
theorem invStab_of_lamEx (hLam : LamEx) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  obtain ⟨μ, hμ⟩ := hSWa1.1
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  obtain ⟨lam, μ0, hμ0, hC, -⟩ :=
    hLam F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have : IsMulRightInvariant μ0 :=
    us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ0 lam s (fun f hf => hC.2 f hf s hs)
  have hc : μ'' = haarScalarFactor μ'' μ0 • μ0 := um_eq_smul_of_sigmaCompact μ'' μ0
  have : IsMulRightInvariant μ'' := by
    refine ⟨fun k => ?_⟩
    rw [hc, Measure.map_smul, map_mul_right_eq_self]
  exact us_invInv μ''

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Establish `hcl` using `us_isClosed_stab F E σ M a J X0`. Establish `: LocallyCompactSpace (stabT (AF F) σ J X0)` using `hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: Countable (HFinIn (AF F) σ J)` using `um_countable_HFinIn F E σ M J`.

Set `f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J` to `fun x => ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`. Establish `e` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (Subtype.ext e)`.

Establish `: Countable (ratIn F E σ M J (stabT (AF F) σ J X0))` using `hinj.countable`. Take `⟨𝓕, h𝓕⟩` from `exFDStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''`. Establish `hfin` using `hFV F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ'' 𝓕 h𝓕`. Establish `: SigmaCompactSpace (stabT (AF F) σ J X0)` using `um_sigmaCompact (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin`. Establish `: IsMulRightInvariant μ''` using `um_rightInv (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin`.

Conclude with `us_invInv μ''`.
-/
theorem invStab_of_finVol (hFV : FinVolStab) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J),
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : Countable (ratIn F E σ M J (stabT (AF F) σ J X0)) := hinj.countable
  obtain ⟨𝓕, h𝓕⟩ :=
    exFDStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have hfin := hFV F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ'' 𝓕 h𝓕
  have : SigmaCompactSpace (stabT (AF F) σ J X0) :=
    um_sigmaCompact (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  have : IsMulRightInvariant μ'' :=
    um_rightInv (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  exact us_invInv μ''

end PI.VolStabS.InvariantStabilizerAssembly
