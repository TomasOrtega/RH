import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV

open Module

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem classFun_char_scalar {G : Type} [Group G] [Fintype G] (e : MonoidAlgebra ℂ G)
    (he : ∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) (ψ : G → ℂ)
    (hψ : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) (x : G) :
    ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  classical
  have hψ' := hψ
  obtain ⟨n, ρ, hρ, rfl⟩ := hψ
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ' hψ'
  rw [if_pos rfl] at horth
  rw [horth] at h1
  have hfr : finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by exact_mod_cast h1.symm
  have hnt : Nontrivial (Fin n → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := hρ.exists_pair_ne
    apply hab
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  let idI : ρ.IntertwiningMap ρ := ⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩
  have hid0 : idI ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    intro h
    have := congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) h
    exact hv this
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := ∑ g : G, e.coeff g • ρ g
  have hTI : ∀ h, T ∘ₗ ρ h = ρ h ∘ₗ T := by
    intro h
    show T * ρ h = ρ h * T
    simp only [T, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    rw [show h⁻¹ * g * h = h⁻¹ * g * h⁻¹⁻¹ by rw [inv_inv], he]
    congr 2
    group
  let TI : ρ.IntertwiningMap ρ := ⟨T, hTI⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr TI
  have hT : T = c • LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc
    simpa [idI, TI] using this.symm
  have htr : ∀ y : G, ∑ g, e.coeff g * ρ.character (g * y) = c * ρ.character y := by
    intro y
    have h2 : T * ρ y = c • ρ y := by rw [hT, smul_mul_assoc]; exact congrArg _ (LinearMap.id_comp _)
    have h3 := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) h2
    simp only [T, Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, smul_eq_mul] at h3
    simpa only [Representation.character] using h3
  have hx := htr x
  have h1' := htr 1
  simp only [mul_one] at h1'
  rw [hx, h1']
  ring

end GlobalTheory
