import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaMinorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSumStatement
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet qminor Tm GlRel)
open CompanionTheory.RgExh

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem continuous_apply_list_prod_ofFn_add_smul : ∀ (m : ℕ) (ℓ : Module.Dual ℂ W) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m
  induction m with
  | zero =>
    intro ℓ A B f
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ m ih =>
    intro ℓ A B f
    have h : (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) =
        fun u : ℂ => (ℓ ∘ₗ A 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) +
          u * (ℓ ∘ₗ B 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) := by
      funext u
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, LinearMap.comp_apply]
    rw [h]
    exact (ih (ℓ ∘ₗ A 0) (fun k => A k.succ) (fun k => B k.succ) f).add
      (continuous_id.mul (ih (ℓ ∘ₗ B 0) (fun k => A k.succ) (fun k => B k.succ) f))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cont_ofFn_prod (ℓ : Module.Dual ℂ W) : ∀ (m : ℕ) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m A B f
  exact continuous_apply_list_prod_ofFn_add_smul m ℓ A B f

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Tm_affine {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (u : ℂ) (k : ℂ) (a b : Fin n) :
    Tm E (u - k) a b = ((if a = b then algebraMap ℂ (Module.End ℂ W) (-k) else 0) + E a b) +
      u • (if a = b then (1 : Module.End ℂ W) else 0) := by
  unfold Tm
  split_ifs with h
  · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_smul]
    abel
  · simp

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cont_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (ℓ : Module.Dual ℂ W) (f : W) :
    Continuous (fun u : ℂ => ℓ (qdet E u f)) := by
  simp only [qdet, qminor, LinearMap.sum_apply, map_sum]
  refine continuous_finsetSum _ fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Tm_affine]
  exact (cont_ofFn_prod ℓ n _ _ f).const_smul _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eq_zero_of_off {g : ℂ → ℂ} (hg : Continuous g) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → g u = 0) : g u₀ = 0 := by
  have hd : Dense ({u₀}ᶜ : Set ℂ) := dense_compl_singleton u₀
  have h0 : g = fun _ => 0 :=
    hg.ext_on hd (continuous_const : Continuous fun _ : ℂ => (0 : ℂ)) (fun u hu => h u hu)
  exact congrFun h0 u₀

end CompanionTheory.RgExh.Hk.UnitPf
