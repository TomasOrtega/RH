import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Establish `hs : ∑ i : Fin N, (τ i : ℕ) = ∑ i : Fin N, (i : ℕ)` using `Equiv.sum_comp τ (fun i => (i : ℕ))`. Use `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin N => (τ i : ℕ)) (g := fun i : Fin N => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)` as an intermediate fact. Conclude with `Fin.ext this`.
-/
theorem perm_apply_eq_of_le {N : ℕ} (τ : Equiv.Perm (Fin N)) (h : ∀ b, τ b ≤ b) (b : Fin N) : τ b = b := by
  have hs : ∑ i : Fin N, (τ i : ℕ) = ∑ i : Fin N, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin N => (τ i : ℕ))
    (g := fun i : Fin N => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

/- English proof (translation)
Introduce `g _ N w w' u u' ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hu hu' h`. Establish `hz : ∀ a b, a ≠ σ b → w.val a b = 0` using `fun a b hab => by`. Assume the negation of the conclusion as `hne`. Conclude with `hab (hσ a b hne)`. Establish `hz' : ∀ a b, a ≠ σ' b → w'.val a b = 0` using `fun a b hab => by`.

Assume the negation of the conclusion as `hne`. Conclude with `hab (hσ' a b hne)`. Establish `hne : ∀ b, w.val (σ b) b ≠ 0`. Introduce `b h0`. Establish `h1 : ((w⁻¹).val * w.val) b b = 1`.

Rewrite using `[Units.inv_mul, Matrix.one_apply_eq]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_zero]`. Conclude with `zero_ne_one h1`. Introduce `k _`. Distinguish the cases in `hk : k = σ b`.

Rewrite using `[hk, h0, mul_zero]`. Rewrite using `[hz k b hk, mul_zero]`. Establish `key : ∀ b, w.val (σ b) b = w'.val (σ b) (σ'.symm (σ b)) * u'.val (σ'.symm (σ b)) b`. Introduce `b`. Establish `h1 : (u.val * w.val) (σ b) b = (w'.val * u'.val) (σ b) b`.

Rewrite using `[← Units.val_mul, ← Units.val_mul, h]`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ b), Finset.sum_eq_single (σ'.symm (σ b)), hu.1, one_mul]`. Conclude with `h1`. Introduce `k _ hk`. Rewrite using `[hz' (σ b) k, zero_mul]`.

Introduce `hh`. Apply `hk` to reduce the goal to its premises. Rewrite using `[hh, Equiv.symm_apply_apply]`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`.

Introduce `k _ hk`. Rewrite using `[hz k b hk, mul_zero]`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Establish `hle : ∀ b, (σ.trans σ'.symm) b ≤ b`.

Introduce `b`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : b < σ'.symm (σ b)` using `not_le.1 hlt`. Apply `hne b` to reduce the goal to its premises. Rewrite using `[key b, hu'.2 _ _ hlt', mul_zero]`.

Establish `hfix : ∀ b, σ'.symm (σ b) = b` using `fun b => perm_apply_eq_of_le _ hle b`. Establish `hσσ : ∀ b, σ b = σ' b` using `fun b => by`. Use `congrArg σ' (hfix b)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `a b`. Distinguish the cases in `hab : a = σ b`. Rewrite using `[hab, key b, hfix b, hu'.1, mul_one]`. Rewrite using `[hz a b hab, hz' a b (by rwa [← hσσ])]`.
-/
theorem monomial_eq_of_unipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  intro g _ N w w' u u' ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hu hu' h
  have hz : ∀ a b, a ≠ σ b → w.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ a b hne)
  have hz' : ∀ a b, a ≠ σ' b → w'.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ' a b hne)
  have hne : ∀ b, w.val (σ b) b ≠ 0 := by
    intro b h0
    have h1 : ((w⁻¹).val * w.val) b b = 1 := by
      rw [Units.inv_mul, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k = σ b
      · rw [hk, h0, mul_zero]
      · rw [hz k b hk, mul_zero]
  have key : ∀ b, w.val (σ b) b = w'.val (σ b) (σ'.symm (σ b)) * u'.val (σ'.symm (σ b)) b := by
    intro b
    have h1 : (u.val * w.val) (σ b) b = (w'.val * u'.val) (σ b) b := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ b),
      Finset.sum_eq_single (σ'.symm (σ b)), hu.1, one_mul] at h1
    · exact h1
    · intro k _ hk
      rw [hz' (σ b) k, zero_mul]
      intro hh
      apply hk
      rw [hh, Equiv.symm_apply_apply]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro k _ hk
      rw [hz k b hk, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hle : ∀ b, (σ.trans σ'.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < σ'.symm (σ b) := not_le.1 hlt
    apply hne b
    rw [key b, hu'.2 _ _ hlt', mul_zero]
  have hfix : ∀ b, σ'.symm (σ b) = b := fun b => perm_apply_eq_of_le _ hle b
  have hσσ : ∀ b, σ b = σ' b := fun b => by
    have := congrArg σ' (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  apply Units.ext
  ext a b
  by_cases hab : a = σ b
  · rw [hab, key b, hfix b, hu'.1, mul_one]
  · rw [hz a b hab, hz' a b (by rwa [← hσσ])]

end GlobalTheory.BadShare
