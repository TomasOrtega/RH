import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

open GlobalTheory.Branching.AddColumn in

/- English proof (translation)
Introduce `K _ _ n ν hν x hx`. Establish `hinj : Function.Injective (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))` using `Function.injective_id.prodMap (Fin.castSucc_injective n)`. Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢`. Take `⟨x', rfl⟩` from `exists_rename_eq_of_vars_subset_range x _ hinj (by`. Introduce and unpack `⟨a, s⟩ hv`.

Proceed by induction on `s using Fin.lastCases with`. Consider the case `cast s => exact ⟨(a, s), rfl⟩`. Consider the case `last`. It suffices to derive a contradiction. Take `⟨d, hd, hvd⟩` from `(mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)`.

Establish `h` using `congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)`. Rewrite `h` using `[hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]`. Establish `h2` using `h _ hvd`. Simplify using `[colW] at h2`. Conclude with `Finsupp.mem_support_iff.1 hvd h2)`.

Use `⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite `hu` using `[← coeff_rename_mapDomain _ hinj]`. Use function extensionality and compare the values at `i`. Rewrite using `[← (weight_mapDomain (n + 1) n u).1, hx.1 hu]`. Establish `h` using `hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)`.

Rewrite `h` using `[colAddGen_rename_castSucc]`. Apply `rename_injective _ (Option.map_injective hinj)` to reduce the goal to its premises. Rewrite using `[h, rename_rename, rename_rename]`. Both sides reduce to the same expression.
-/
theorem exists_eq_incl_of_last_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  intro K _ _ n ν hν x hx
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢
  obtain ⟨x', rfl⟩ := exists_rename_eq_of_vars_subset_range x _ hinj (by
    rintro ⟨a, s⟩ hv
    induction s using Fin.lastCases with
    | cast s => exact ⟨(a, s), rfl⟩
    | last =>
      exfalso
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h := congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)
      rw [hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff] at h
      have h2 := h _ hvd
      simp [colW] at h2
      exact Finsupp.mem_support_iff.1 hvd h2)
  refine ⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩
  · rw [← coeff_rename_mapDomain _ hinj] at hu
    funext i
    rw [← (weight_mapDomain (n + 1) n u).1, hx.1 hu]
  · have h := hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)
    rw [colAddGen_rename_castSucc] at h
    apply rename_injective _ (Option.map_injective hinj)
    rw [h, rename_rename, rename_rename]
    rfl

end GlobalTheory.BrCompare
