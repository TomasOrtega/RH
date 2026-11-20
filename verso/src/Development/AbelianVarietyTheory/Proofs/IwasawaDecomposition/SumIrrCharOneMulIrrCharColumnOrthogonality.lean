import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CyclicSplitting.IrrDecomp

open Formalism.L2.DIV

namespace GlobalTheory.ColumnOrth

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/- English proof (translation)
Unfold `Representation.character`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]`. Distinguish the cases in `h : g = 1`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Establish `hx : g * x ≠ x` using `by simpa using h`. Simplify using `[Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis, hx]`.
-/
theorem leftRegular_character (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  by_cases h : g = 1
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : g * x ≠ x := by simpa using h
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis, hx]

/- English proof (translation)
Take `⟨r, d, τ, hirr, hch⟩` from `CycSplitWork.char_eq_sum_irreducible (G := G) (L := ℂ) (Representation.leftRegular ℂ G)`. Use `set χ : Fin r → (G → ℂ) := fun i => (τ i).character with hχ`. Establish `hmem : ∀ i, χ i ∈ A` using `fun i => (hA _).2 ⟨d i, τ i, hirr i, rfl⟩`. Establish `hcard : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hmult : ∀ ψ ∈ A, (({i | χ i = ψ} : Finset (Fin r)).card : ℂ) = ψ 1`.

Introduce `ψ hψ`. Establish `hψ'` using `(hA ψ).1 hψ`. Establish `h1 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ = ψ 1`. Repeatedly rewrite using `[leftRegular_character, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ (1 : G)]`.

Simplify using `[Nat.card_eq_fintype_card, hcard]`. Establish `h2 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ = ∑ i, if χ i = ψ then (1 : ℂ) else 0`. Repeatedly rewrite using `[hch, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `Formalism.L2.Col.gx_orth ⟨d i, τ i, hirr i, rfl⟩ hψ'` and compare the differences between its conclusion and the goal. Rewrite using `[← h1, h2, Finset.sum_boole]`. Establish `hr` using `leftRegular_character (G := G) g`. Rewrite `hr` using `[hch g]`. Rewrite using `[← hr, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := A) (fun i _ => hmem i)]`.

Use `Finset.sum_congr rfl fun ψ hψ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => ψ g) fun i hi => congrFun (Finset.mem_filter.1 hi).2 g, Finset.sum_const, nsmul_eq_mul, hmult ψ hψ]`.
-/
theorem sum_char_one_mul_char (A : Finset (G → ℂ))
    (hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) (g : G) :
    ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  obtain ⟨r, d, τ, hirr, hch⟩ :=
    CycSplitWork.char_eq_sum_irreducible (G := G) (L := ℂ) (Representation.leftRegular ℂ G)
  set χ : Fin r → (G → ℂ) := fun i => (τ i).character with hχ
  have hmem : ∀ i, χ i ∈ A := fun i => (hA _).2 ⟨d i, τ i, hirr i, rfl⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmult : ∀ ψ ∈ A, (({i | χ i = ψ} : Finset (Fin r)).card : ℂ) = ψ 1 := by
    intro ψ hψ
    have hψ' := (hA ψ).1 hψ
    have h1 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ = ψ 1 := by
      simp_rw [leftRegular_character, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp [Nat.card_eq_fintype_card, hcard]
    have h2 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ =
        ∑ i, if χ i = ψ then (1 : ℂ) else 0 := by
      simp_rw [hch, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      convert Formalism.L2.Col.gx_orth ⟨d i, τ i, hirr i, rfl⟩ hψ'
    rw [← h1, h2, Finset.sum_boole]
  have hr := leftRegular_character (G := G) g
  rw [hch g] at hr
  rw [← hr, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := A) (fun i _ => hmem i)]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ψ g) fun i hi => congrFun (Finset.mem_filter.1 hi).2 g, Finset.sum_const, nsmul_eq_mul,
    hmult ψ hψ]

end GlobalTheory.ColumnOrth
