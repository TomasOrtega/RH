import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem linearIndependent_conj_eigenmatrices {Γ k ι : Type} [Group Γ] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (ψ : ι → Γ →* k) (hψ : Function.Injective ψ)
    (X : ι → Matrix (Fin n) (Fin n) k) (hX : ∀ i, X i ≠ 0)
    (h : ∀ i g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X i =
      ψ i g • (X i * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    LinearIndependent k X := by
  have hli : LinearIndependent k (fun i => (ψ i : Γ → k)) :=
    (linearIndependent_monoidHom Γ k).comp ψ hψ
  rw [linearIndependent_iff'] at hli ⊢
  intro s c hc i hi
  have key : ∀ g, ∑ j ∈ s, (c j * ψ j g) • X j = 0 := by
    intro g
    have h1 : (∑ j ∈ s, (c j * ψ j g) • X j) *
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      have h2 : ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (∑ j ∈ s, c j • X j) = 0 := by
        rw [hc, Matrix.mul_zero]
      rw [← h2, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, h, smul_smul, smul_mul_assoc]
    exact (Units.mul_left_eq_zero (r g)).1 h1
  by_contra hci
  apply hX i
  ext a b
  have h3 := hli s (fun j => c j * X j a b) (by
    funext g
    have h4 := congrFun (congrFun (key g) a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun j _ => by ring) i hi
  simpa [hci] using h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem finite_quadratic_characters_in_adjoint :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k),
      Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  intro Γ k _ _ _ n r
  set S := {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} with hS
  have hex : ∀ χ : S, ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ.1 g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :=
    fun χ => χ.2
  choose X hX h using hex
  let ψ : S → Γ →* k := fun χ =>
    ((Int.castRingHom k).toMonoidHom.comp (Units.coeHom ℤ)).comp χ.1
  have hψ : Function.Injective ψ := by
    intro χ₁ χ₂ e
    apply Subtype.ext
    ext g
    have h1 : ((χ₁.1 g : ℤ) : k) = ((χ₂.1 g : ℤ) : k) := DFunLike.congr_fun e g
    exact_mod_cast h1
  have hli := linearIndependent_conj_eigenmatrices r ψ hψ X hX h
  have : Finite S := hli.finite_of_isNoetherian
  exact Set.toFinite S

end GlobalTheory
