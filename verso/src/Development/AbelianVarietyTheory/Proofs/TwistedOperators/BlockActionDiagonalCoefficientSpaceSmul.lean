import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Formalism.GradedWeylDivisibility.FinalD

open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type_right]`. Rewrite using `[Finset.sum_eq_single t]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW]`. Introduce `s _ hs`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]`. Simplify using the standard rewrite rules.
-/
lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

/- English proof (translation)
Establish `hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1`. Use extensionality with `m`. Rewrite using `[Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]`. Distinguish the cases in `h : coeff m F = 0`. Simplify using `[h]`.

Establish `hm` using `hw h`. Rewrite using `[Finset.prod_pow_eq_pow_sum, mul_comm]`. Use `congr 2`. Simplify using `only [Formalism.GradedWeylDivisibility.rowDeg]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← weight_colW_apply, hm]`.
-/
theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]
  by_cases h : coeff m F = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

/- English proof (translation)
Unfold `Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ`. Proceed by induction on `hQ using Submodule.span_induction with`. Consider the case `mem P hP`. Take `⟨F, hF, rfl⟩` from `hP`. Establish `h1` using `(Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1`.

Rewrite using `[map_prod]`. Repeatedly rewrite using `[h1]`. Establish `h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) = c τ ^ (∑ a, (lam τ).natW a) • F τ` using `fun τ => GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)`. Repeatedly rewrite using `[h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `smul a x _ hx => rw [map_smul, hx, smul_comm]`.
-/
theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
