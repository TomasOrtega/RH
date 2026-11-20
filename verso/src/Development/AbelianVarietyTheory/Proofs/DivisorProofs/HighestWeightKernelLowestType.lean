import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FockWeightWedgeLowerModes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TensFockInfPhysSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

/- English proof (translation)
Introduce `n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS`. Establish `hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z`. Establish `e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) = fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b)`. Use function extensionality and compare the values at `a b`. Simplify using `only [diagE, eT, sgE_cpT]`.

Rewrite using `[← e]`. Conclude with `hz`. Take `⟨s, hy0, hy⟩` from `khw_extract ε hg.1 hz' hz0`. Use `set y := tcoef ((fockBasis n).coord s) z with hydef`. Establish `hs : s ⊆ lfPhysModes ε`.

Introduce `m hm`. Assume the negation of the conclusion as `hnm`. Apply `hy0` to reduce the goal to its premises. Use `tco_physSub_zero hzp hm fun hp => hnm ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `finProdFinEquiv.surjective m`.

Rewrite `hp` using `[Equiv.symm_apply_apply]`. Conclude with `(lf_mem_phys ε x.1 x.2).2 hp`. Use `set Ph := gcPh ε s with hPh`. Establish `hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph`. Rewrite using `[gc_wt_eq ε hs]`.

Use function extensionality and compare the values at `a`. Simplify using `only [gaW, lowK, Pi.sub_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hy` using `[hwt]`. Establish `hyS : y ∈ S` using `hzS s`.

Use `set V := kLowSpan ε E y with hV`. Establish `hVS : V ≤ S` using `kLowSpan_le hSk hyS`. Use `haveI : FiniteDimensional ℂ S := hSfd`. Establish `hVfd : FiniteDimensional ℂ V` using `Submodule.finiteDimensional_of_le hVS`. Establish `hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V` using `kLowSpan_kIrrHW hE hU hy hy0 hVfd`.

Use `set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT`. Establish `hTk : IsKStableSub ε E T`. Introduce `a b _ v hv`. Rewrite `hv`, the goal using `[hT, LinearMap.mem_ker]`. Establish `hc` using `congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)`.

Simplify using `only [Module.End.mul_apply] at hc`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢`. Rewrite using `[hc, sub_eq_zero.1 hv, map_smul, sub_self]`. Establish `hyT : y ∈ T`. Rewrite using `[hT, LinearMap.mem_ker]`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Rewrite using `[hcas s, sub_self]`. Establish `hVT : V ≤ T` using `kLowSpan_le hTk hyT`. Establish `hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v`. Introduce `v hv`.

Use `hVT hv` as an intermediate fact. Rewrite `this` using `[hT, LinearMap.mem_ker]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this`. Conclude with `sub_eq_zero.1 this`. Establish `hPh0 : Ph = ∅`.

Assume the negation of the conclusion as `hne`. Conclude with `dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc`. Rewrite `hVirr` using `[hPh0]`. Simplify using `only [phSum, Finset.sum_empty, sub_zero] at hVirr`. Use `⟨V, hVirr, ?_, hVc⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Establish `: y ∈ V` using `self_mem_kLowSpan y`. Rewrite `this` using `[h0]`. Conclude with `(Submodule.mem_bot ℂ).1 this`.
-/
theorem highestWeightKernel_lowestType : AlgDatum := by
  intro n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS

  have hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z := by
    have e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) =
        fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
      funext a b
      simp only [diagE, eT, sgE_cpT]
    rw [← e]; exact hz
  obtain ⟨s, hy0, hy⟩ := khw_extract ε hg.1 hz' hz0
  set y := tcoef ((fockBasis n).coord s) z with hydef

  have hs : s ⊆ lfPhysModes ε := by
    intro m hm
    by_contra hnm
    apply hy0
    refine tco_physSub_zero hzp hm fun hp => hnm ?_
    obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
    rw [Equiv.symm_apply_apply] at hp
    exact (lf_mem_phys ε x.1 x.2).2 hp
  set Ph := gcPh ε s with hPh
  have hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph := by
    rw [gc_wt_eq ε hs]
    funext a
    simp only [gaW, lowK, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hwt] at hy
  have hyS : y ∈ S := hzS s
  set V := kLowSpan ε E y with hV
  have hVS : V ≤ S := kLowSpan_le hSk hyS
  haveI : FiniteDimensional ℂ S := hSfd
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V := kLowSpan_kIrrHW hE hU hy hy0 hVfd

  set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT
  have hTk : IsKStableSub ε E T := by
    intro a b _ v hv
    rw [hT, LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at hc
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [hc, sub_eq_zero.1 hv, map_smul, sub_self]
  have hyT : y ∈ T := by
    rw [hT, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hcas s, sub_self]
  have hVT : V ≤ T := kLowSpan_le hTk hyT
  have hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    have := hVT hv
    rw [hT, LinearMap.mem_ker] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this

  have hPh0 : Ph = ∅ := by
    by_contra hne
    exact dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc
  rw [hPh0] at hVirr
  simp only [phSum, Finset.sum_empty, sub_zero] at hVirr
  refine ⟨V, hVirr, ?_, hVc⟩
  intro h0
  apply hy0
  have : y ∈ V := self_mem_kLowSpan y
  rw [h0] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.PsCo.PcEF
