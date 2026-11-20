import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using `only [vol0, ExteriorAlgebra.ιMulti_apply]`. Rewrite using `[map_list_prod]`. Use `congr 1`. Simplify using `only [List.map_ofFn]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Establish `h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w` using `fun w => by`. Simplify using `[mapDR]`. Establish `h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a))` using `fun a => by`. Simplify using `[map1, ι1, KaehlerDifferential.map_D]`.

Simplify using `only [Function.comp, h1, map_smul, h2, map_inv₀]`. Rewrite using `[← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]`.
-/
private theorem kahlerMap_volumeForm {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
    [IsScalarTower ℂ F K'] {d : ℕ} (x : Fin (d + 1) → F) :
    mapDR ℂ K K' (vol0 ℂ K x) = vol0 ℂ K' x := by
  simp only [vol0, ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext j
  have h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w := fun w => by
    simp [mapDR]
  have h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a)) := fun a => by
    simp [map1, ι1, KaehlerDifferential.map_D]
  simp only [Function.comp, h1, map_smul, h2, map_inv₀]
  rw [← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Introduce `F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ`. Use `haveI : FiniteDimensional F K := hY.covZ.fin`. Use `haveI : FiniteDimensional F K' := hY.covY.fin`. Use `haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'`. Establish `hTr` using `(GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1`.

Establish `second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h)`. Introduce `h`. Rewrite using `[← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]`. Simplify using `only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]`. Rewrite using `[Algebra.trace_trace]`.

Use `⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y', hy', rfl⟩`. Take `⟨⟨τ', hτ'⟩, hvol⟩` from `GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY`. Establish `key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0`. Introduce `i`.

Establish `hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧ (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K'))` using `hy' (Finset.univ.erase i) (Set.mem_univ _)`. Distinguish the cases in `hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty`. Establish `hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1`. Simplify using the standard rewrite rules. Rewrite `hm` using `[if_pos ⟨hne, hc⟩]`.

Establish `hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, v, -, rfl⟩`. Use `(⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_` and prove the remaining obligations. Rewrite using `[← ExteriorAlgebra.ιMulti_span_fixedDegree]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Rewrite using `[hvol τ' hτ' _ (hle hm), second]`. Establish `h1` using `(GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1 (one_mem _)`. Rewrite `h1` using `[mul_one]`. Conclude with `GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1`.

Rewrite `hm` using `[if_neg (fun h => hne h.1)]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hm]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0`. Simplify using `only [map_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, key i, smul_zero]`.
-/
theorem UpperTheory.Gal.productCup_of_system.trTop_of :
    TrTop := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ
  haveI : FiniteDimensional F K := hY.covZ.fin
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'
  have hTr := (GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1
  have second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h) := by
    intro h
    rw [← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]
    rw [Algebra.trace_trace]
  refine ⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨⟨τ', hτ'⟩, hvol⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY
  have key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0 := by
    intro i
    have hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧
        (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then
        omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K')) :=
      hy' (Finset.univ.erase i) (Set.mem_univ _)
    by_cases hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty
    · have hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 := by
        simp
      rw [if_pos ⟨hne, hc⟩] at hm
      have hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, -, v, -, rfl⟩
        refine (⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hvol τ' hτ' _ (hle hm), second]
      have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1
        (one_mem _)
      rw [mul_one] at h1
      exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1
    · rw [if_neg (fun h => hne h.1)] at hm
      rw [(Submodule.mem_bot ℂ).1 hm]
      simp
  change trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0
  simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_zsmul, key i, smul_zero]
