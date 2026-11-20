import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hψ a ha b hb`. Establish `P` using `GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k`. Take `⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩` from `P`. Unfold `theta`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `ht : Triv (ψ m / nxt ψ m) 1`. Rewrite using `[hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]`. Take `⟨hv, hc⟩` from `GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k n ψ hψ m ht`. Establish `hab` using `GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hψ a ha b hb`.

Establish `va` using `hv a ha`. Establish `vb` using `hv b hb`. Establish `vab` using `hv (a * b) hab`. Establish `vprod : valuation k (minor a m * minor b m) = 1` using `by rw [map_mul, va, vb, one_mul]`. Rewrite using `[hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]`.
-/
theorem theta_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  intro k _ _ _ _ n ψ hψ a ha b hb
  have P := GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k
  obtain ⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩ := P
  unfold theta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases ht : Triv (ψ m / nxt ψ m) 1
  · rw [hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]
  · obtain ⟨hv, hc⟩ := GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k n ψ hψ m ht
    have hab := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hψ a ha b hb
    have va := hv a ha
    have vb := hv b hb
    have vab := hv (a * b) hab
    have vprod : valuation k (minor a m * minor b m) = 1 := by rw [map_mul, va, vb, one_mul]
    rw [hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]

end GlobalTheory.PsType
