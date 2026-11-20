import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Rewrite using `[Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]`. Conclude with `AddSubgroup.mem_zmultiples 1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ModularGroup.T ∈ Gamma1 N`. Rewrite using `[CongruenceSubgroup.Gamma1_mem]`.

Simplify using `[ModularGroup.T]`. Use `show ModularGroup.T ∈ Gamma0 l`. Rewrite using `[CongruenceSubgroup.Gamma0_mem]`. Simplify using `[ModularGroup.T]`.
-/
theorem one_mem_strictPeriods_lev (N l : ℕ) :
    (1 : ℝ) ∈ ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]
  · exact AddSubgroup.mem_zmultiples 1
  · refine ⟨?_, ?_⟩
    · show ModularGroup.T ∈ Gamma1 N
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · show ModularGroup.T ∈ Gamma0 l
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

/- English proof (translation)
Introduce `N l k _ f τ`. Establish `h1` using `one_mem_strictPeriods_lev N l`. Use `haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩`. Conclude with `ModularForm.hasSum_qExpansion f one_pos h1 τ`.
-/
theorem lev_hasSum_coef : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (lev N l) k) (τ : ℍ),
    HasSum (fun m => coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  intro N l k _ f τ
  have h1 := one_mem_strictPeriods_lev N l
  haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

end GlobalTheory.Hk
