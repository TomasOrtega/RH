import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesProjLattice

/- English proof (translation)
Unfold `coordProj`. Rewrite using `[LinearMap.coe_comp]`. Conclude with `(LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp B.equivFun.surjective`.
-/
theorem coordProj_surjective {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by
  unfold coordProj
  rw [LinearMap.coe_comp]
  exact (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [coordProj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.funLeft_apply, Module.Basis.equivFun_self]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
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
Introduce `K _ _ n m k a B τ ha hB hτ`. Take `⟨hfg, hspan⟩` from `h1 K n a ha`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hfg.map ((coordProj B).restrictScalars (𝓞 K))).restrictScalars`. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `coordProj_surjective B`. Introduce `v hv`. Establish `hv' : ∀ j, v j ∈ (a (τ j) : Submodule (𝓞 K) K)` using `fun j => (Submodule.mem_pi (I := Set.univ)).1 hv j (Set.mem_univ j)`. Use `⟨∑ j, v j • (Pi.single (τ j) 1 : Fin n → K), ?_, ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_pi (I := Set.univ)).2 fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_apply]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : τ j = x`. Substitute `h` using the available equality. Simplify using `using hv' j`.

Simplify using `[Pi.single_eq_of_ne' h]`. Simplify using `only [LinearMap.restrictScalars_apply, map_sum, map_smul, ← hB, coordProj_basis_inr]`. Use extensionality with `i`. Simplify using `[Pi.single_apply]`.
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
