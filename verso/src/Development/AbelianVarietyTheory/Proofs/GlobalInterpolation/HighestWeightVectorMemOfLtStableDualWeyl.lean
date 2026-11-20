import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModuleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightModStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineFieldStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEqStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDominantHighestVectorOfLtStableStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmulStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `[Pi.single_apply]`.
-/
theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply]

/- English proof (translation)
Introduce `p hp k _ _ N ν hν hal M M' hM hM' hlt hle`. Establish `dom` using `GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν`. Take `⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩` from `GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩`. Establish `hv0 : v ≠ 0` using `fun h => hvM (h ▸ zero_mem M)`. Establish `hwt` using `GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw`.

Establish `hrel` using `(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1`. Establish `hhw` using `GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf) (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)`. Establish `hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j`. Introduce `j`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hhw j`. Establish `h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v` using `GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')`. Express the relevant statement in the definitionally equal form `gel k N N j v - _ ∈ M at h1`. Rewrite `h1` using `[h2, ← sub_smul]`. Conclude with `hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)`.

Take `⟨m, hm⟩ : v.support.Nonempty` from `Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])`. Establish `hmμ : ∀ a, μ a = rowDeg m a` using `fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)`. Establish `hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p`. Introduce `h`. Use `⟨(hal h).1, ?_, (hal h).2⟩` and prove the remaining obligations.

Establish `hd` using `(dom v (hle hvM') m hm).1 1`. Establish `hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩}`. Use extensionality with `a`. Simplify using `[Fin.ext_iff]`. Rewrite `hd` using `[hs, Finset.sum_singleton, Finset.sum_singleton]`.

Rewrite using `[hmμ]`. Conclude with `hd`. Establish `hμν : μ = ν` using `GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq p hp k N ν μ hν hμ hcond hval`. Substitute `hμν` using the available equality. Take `⟨c, hc⟩` from `GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hv0 (by rw [hc, zero_smul])`. Use `⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩` and prove the remaining obligations. Establish `: hw k le_rfl μ = c⁻¹ • v` using `by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[this]`. Conclude with `M'.smul_mem _ hvM'`.
-/
theorem hw_mem_of_lt : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  intro p hp k _ _ N ν hν hal M M' hM hM' hlt hle
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p := by
    intro h
    refine ⟨(hal h).1, ?_, (hal h).2⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq p hp k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

end GlobalTheory.Alc
