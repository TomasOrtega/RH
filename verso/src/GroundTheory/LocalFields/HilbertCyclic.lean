import Mathlib
import GroundTheory.LocalFields.CompleteTrivial

namespace GroundTheory.LocalField

open Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Partial

variable (σ : L ≃ₐ[K] L) (x : Lˣ)

noncomputable def partialNorm (m : ℕ) : Lˣ :=
  ∏ j ∈ range m, (σ ^ j) • x

omit [FiniteDimensional K L] in
/- English proof (translation)
Rewrite using `[partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']`. Repeatedly rewrite using `[pow_add, mul_smul]`.
-/
theorem partialNorm_add (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by
  rw [partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']
  simp_rw [pow_add, mul_smul]

omit [FiniteDimensional K L] in
/- English proof (translation)
Rewrite using `[partialNorm, prod_range_one, pow_zero, one_smul]`.
-/
theorem partialNorm_one : partialNorm σ x 1 = x := by
  rw [partialNorm, prod_range_one, pow_zero, one_smul]

variable {σ}

/- English proof (translation)
Rewrite using `[partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]`. Use `Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)` and prove the remaining obligations. Introduce `i j hij`. Conclude with `Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)`. Introduce `g`.

Take `⟨k, hk⟩` from `(mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)`. Use `⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ ^ (k % orderOf σ) = g`. Rewrite using `[pow_mod_orderOf]`. Conclude with `hk`.
-/
theorem partialNorm_orderOf (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    partialNorm σ x (orderOf σ) = tateNorm (L ≃ₐ[K] L) Lˣ x := by
  rw [partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]
  refine Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _
    (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  · intro g
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    refine ⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩
    change σ ^ (k % orderOf σ) = g
    rw [pow_mod_orderOf]
    exact hk

variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx

/- English proof (translation)
Rewrite using `[add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]`.
-/
theorem partialNorm_add_orderOf (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by
  rw [add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]

/- English proof (translation)
Use `conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]`. Proceed by induction on `m / orderOf σ with`. Consider the case `zero => simp`. Consider the case `succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]`.
-/
theorem partialNorm_mod (m : ℕ) : partialNorm σ x (m % orderOf σ) = partialNorm σ x m := by
  conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]
  induction m / orderOf σ with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]

/- English proof (translation)
Rewrite using `[← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]`.
-/
theorem partialNorm_eq_of_pow_eq {a b : ℕ} (h : σ ^ a = σ ^ b) :
    partialNorm σ x a = partialNorm σ x b := by
  rw [← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]

end Partial

/- English proof (translation)
Establish `hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g` using `fun g => by`. Take `⟨k, hk⟩` from `(mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)`. Conclude with `⟨k, hk⟩`. Use `choose k hk using hk`. Set `f : (L ≃ₐ[K] L) → Lˣ` to `fun g => partialNorm σ x (k g)`.

Establish `hf : groupCohomology.IsMulCocycle₁ f`. Introduce `g h`. Establish `e : σ ^ k (g * h) = σ ^ (k g + k h)` using `by rw [hk, pow_add, hk, hk]`. Express the relevant statement in the definitionally equal form `partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)`. Rewrite using `[partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]`.

Take `⟨β, hβ⟩` from `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf`. Use `⟨β, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ σ]`. Express the relevant statement in the definitionally equal form `partialNorm σ x (k σ) = x`. Rewrite using `[partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]`.
-/
theorem exists_smul_div_eq_of_tateNorm_eq_one {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  have hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    exact ⟨k, hk⟩
  choose k hk using hk
  let f : (L ≃ₐ[K] L) → Lˣ := fun g => partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have e : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    change partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)
    rw [partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  rw [hβ σ]
  change partialNorm σ x (k σ) = x
  rw [partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := L ≃ₐ[K] L)`. Rewrite using `[subsingleton_tateNegOne_iff]`. Introduce `x hx`. Take `⟨y, hy⟩` from `exists_smul_div_eq_of_tateNorm_eq_one hσ hx`. Conclude with `Subgroup.subset_closure ⟨σ, y, hy⟩`.
-/
theorem subsingleton_tateNegOne_units [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hσ hx
  exact Subgroup.subset_closure ⟨σ, y, hy⟩

end GroundTheory.LocalField
