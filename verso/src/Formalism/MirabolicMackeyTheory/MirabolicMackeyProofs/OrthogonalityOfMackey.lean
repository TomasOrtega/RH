import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem orthogonality_of_mackey : OrthOfMackey := by
  unfold OrthOfMackey
  intro K _ _ _ Z _ _ P _ _ ρ U _ ψ hM h hh z hz
  obtain ⟨_, hmul, hex⟩ := hM
  obtain ⟨u0, hu0, hc, hne⟩ := hex h hh
  set S := ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) with hS
  have hz' : ∀ u ∈ U, ρ u z = ((ψ u : 𝓞 K) : K) • z := by
    intro u hu
    unfold eig at hz
    have h1 := (Submodule.mem_iInf _).mp hz ⟨u, hu⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h1
    exact h1
  have hA : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ u0 : 𝓞 K) : K) • S := by
    rw [hS, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    have key : ψ ((u : P)⁻¹) = ψ u0 * ψ (((u : P) * u0)⁻¹) := by
      rw [← hmul u0 hu0 _ (U.inv_mem (U.mul_mem u.2 hu0))]
      congr 1
      group
    rw [key]
    norm_cast
  have hB : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • S := by
    have e1 : ρ u0 (ρ h z) = ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • ρ h z := by
      have e2 : ρ u0 (ρ h z) = ρ h (ρ (h⁻¹ * u0 * h) z) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [e2, hz' _ hc, map_smul]
    rw [hS, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [e1, map_smul, smul_smul, smul_smul, mul_comm]
  have h3 : (((ψ u0 : 𝓞 K) : K) - ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K)) • S = 0 := by
    rw [sub_smul, ← hA, ← hB, sub_self]
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact absurd (by exact_mod_cast (sub_eq_zero.mp h0).symm) hne
  · exact h0

end Formalism.EigenvalueLevelCeiling
