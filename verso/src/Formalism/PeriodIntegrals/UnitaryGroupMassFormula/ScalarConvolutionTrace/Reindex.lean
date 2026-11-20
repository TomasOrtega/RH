import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic Finset

/- English proof (translation)
Unfold `gam`. Use `congr 1`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight g) (fun y => psiNat ψ₀ (y * x * y⁻¹))]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`.

Use `congr 1`. Use `group`.
-/
theorem gam_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (g x : GL (Fin k) F) :
    gam ψ₀ (g * x * g⁻¹) = gam ψ₀ x := by
  unfold gam
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun y => psiNat ψ₀ (y * x * y⁻¹))]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group

/- English proof (translation)
Introduce `F _ _ k ψ₀ V _ _ π g`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [repGam, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Establish `hm : ∀ a b : GL (Fin k) F, π a (π b v) = π (a * b) v` using `fun a b => by`.

Rewrite using `[map_mul, Module.End.mul_apply]`. Simplify using `only [hm]`. Rewrite using `[← Equiv.sum_comp (MulAut.conj g).toEquiv (fun x => gam ψ₀ x • π (x * g) v)]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`.

Rewrite using `[gam_conj]`. Use `congr 2`. Use `group`.
-/
theorem representation_commutes_gamma : RepGamComm := by
  intro F _ _ k ψ₀ V _ _ π g
  apply LinearMap.ext
  intro v
  simp only [repGam, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have hm : ∀ a b : GL (Fin k) F, π a (π b v) = π (a * b) v := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  simp only [hm]

  rw [← Equiv.sum_comp (MulAut.conj g).toEquiv (fun x => gam ψ₀ x • π (x * g) v)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [gam_conj]
  congr 2
  group

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`.
-/
theorem representation_conjugation_apply {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V) (y x : GL (Fin k) F) (v : V) :
    π y⁻¹ (π (y * x * y⁻¹) (π y v)) = π x v := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/- English proof (translation)
Introduce `F _ _ k ψ₀ V _ _ π`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `hR : ∀ y : GL (Fin k) F, ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) v = ∑ z, ((cardU F k : ℂ)⁻¹ * psiNat ψ₀ (y * z * y⁻¹)) • π z v`. Introduce `y`.

Simplify using `only [projQ, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]`. Rewrite using `[← Equiv.sum_comp (MulAut.conj y).toEquiv, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Rewrite using `[representation_conjugation_apply, smul_smul]`.

Simplify using `only [repGam, gam, LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[Finset.sum_congr rfl fun y _ => hR y, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_smul]`.
-/
theorem representation_conjugate_gamma : RepGamConj := by
  intro F _ _ k ψ₀ V _ _ π
  apply LinearMap.ext
  intro v
  have hR : ∀ y : GL (Fin k) F, ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) v =
      ∑ z, ((cardU F k : ℂ)⁻¹ * psiNat ψ₀ (y * z * y⁻¹)) • π z v := by
    intro y
    simp only [projQ, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    rw [← Equiv.sum_comp (MulAut.conj y).toEquiv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [representation_conjugation_apply, smul_smul]
  simp only [repGam, gam, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun y _ => hR y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]

/- English proof (translation)
Introduce `F _ _ k ψ₀ V _ _ _ π`. Rewrite using `[representation_conjugate_gamma F k ψ₀ V π, map_sum]`. Establish `h : ∀ y : GL (Fin k) F, LinearMap.trace ℂ V ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) = LinearMap.trace ℂ V (projQ ψ₀ π)`. Introduce `y`. Use `show LinearMap.trace ℂ V (π y⁻¹ * (projQ ψ₀ π * π y)) = _`.

Rewrite using `[LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`. Rewrite using `[Finset.sum_congr rfl fun y _ => h y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem trace_representation_gamma : TraceRepGam := by
  intro F _ _ k ψ₀ V _ _ _ π
  rw [representation_conjugate_gamma F k ψ₀ V π, map_sum]

  have h : ∀ y : GL (Fin k) F,
      LinearMap.trace ℂ V ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) = LinearMap.trace ℂ V (projQ ψ₀ π) := by
    intro y
    show LinearMap.trace ℂ V (π y⁻¹ * (projQ ψ₀ π * π y)) = _
    rw [LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PI.GGConvScalarW
