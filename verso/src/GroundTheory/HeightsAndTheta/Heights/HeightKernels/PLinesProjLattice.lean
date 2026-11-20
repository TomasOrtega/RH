import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesProjLattice

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coordProj_surjective {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by
  unfold coordProj
  rw [LinearMap.coe_comp]
  exact (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem coordProj_basis_inr {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (j : Fin k) :
    coordProj B (B (Sum.inr j)) = Pi.single j 1 := by
  ext i
  simp only [coordProj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.funLeft_apply, Module.Basis.equivFun_self]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end KLinesProjLattice

open KLinesProjLattice in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem LinesProjLattice.proof (h1 : LinesIdealLatticeFG.Statement) : LinesProjLattice.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hfg, hspan⟩ := h1 K n a ha
  refine ⟨?_, ?_, ?_⟩
  · exact (hfg.map ((coordProj B).restrictScalars (𝓞 K))).restrictScalars
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan,
      Submodule.map_top, LinearMap.range_eq_top]
    exact coordProj_surjective B
  · intro v hv
    have hv' : ∀ j, v j ∈ (a (τ j) : Submodule (𝓞 K) K) := fun j =>
      (Submodule.mem_pi (I := Set.univ)).1 hv j (Set.mem_univ j)
    refine ⟨∑ j, v j • (Pi.single (τ j) 1 : Fin n → K), ?_, ?_⟩
    · refine (Submodule.mem_pi (I := Set.univ)).2 fun x _ => ?_
      rw [Finset.sum_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases h : τ j = x
      · subst h; simpa using hv' j
      · simp [Pi.single_eq_of_ne' h]
    · simp only [LinearMap.restrictScalars_apply, map_sum, map_smul, ← hB, coordProj_basis_inr]
      ext i
      simp [Pi.single_apply]

end GroundTheory.Heights₂.Heights
