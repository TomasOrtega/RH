import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

open Polynomial in

/- English proof (translation)
Introduce `G _ _ χ hχc H hH g`. Take `⟨n, ρ, hρ⟩` from `hχc`. Use `Fintype.ofFinite H` as an intermediate fact. Establish `hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x)` using `fun x => by`. Simplify using `[hρ, Representation.character]`.

Rewrite `hH`, the goal using `[finsum_eq_sum_of_fintype]`. Simplify using `only [hχ] at hH ⊢`. Rewrite `hH` using `[← map_sum]`. Use `set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS`. Establish `habs : ∀ v : H, ρ v * S = S`.

Introduce `v`. Rewrite using `[hS, Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)` and prove the remaining obligations. Simplify using `[map_mul]`. Establish `hcard : (Fintype.card H : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Establish `hSS : S * S = (Fintype.card H : ℂ) • S` using `by conv_lhs => arg 1; rw [hS]`. Rewrite using `[Finset.sum_mul]`. Simplify using `only [habs, Finset.sum_const, Finset.card_univ]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Establish `hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S)`.

Unfold `IsIdempotentElem`. Rewrite using `[smul_mul_smul, hSS, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hP : (Fintype.card H : ℂ)⁻¹ • S = 0` using `(LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])`.

Establish `hS0 : S = 0` using `by simpa [hcard] using hP`. Establish `hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S)`. Rewrite using `[Finset.mul_sum, map_sum]`. Simplify using `[map_mul]`. Rewrite using `[hsum, hS0, mul_zero, map_zero]`.
-/
theorem _root_.GlobalTheory.BI.char_coset_sum_eq_zero :
    ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ χ → ∀ H : Subgroup G,
      ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  intro G _ _ χ hχc H hH g
  obtain ⟨n, ρ, hρ⟩ := hχc
  have := Fintype.ofFinite H
  have hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x) := fun x => by
    simp [hρ, Representation.character]
  rw [finsum_eq_sum_of_fintype] at hH ⊢
  simp only [hχ] at hH ⊢
  rw [← map_sum] at hH
  set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS
  have habs : ∀ v : H, ρ v * S = S := by
    intro v
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
    simp [map_mul]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hSS : S * S = (Fintype.card H : ℂ) • S := by
    conv_lhs => arg 1; rw [hS]
    rw [Finset.sum_mul]
    simp only [habs, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S) := by
    unfold IsIdempotentElem
    rw [smul_mul_smul, hSS, smul_smul]
    congr 1
    field_simp
  have hP : (Fintype.card H : ℂ)⁻¹ • S = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])
  have hS0 : S = 0 := by simpa [hcard] using hP
  have hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S) := by
    rw [Finset.mul_sum, map_sum]
    simp [map_mul]
  rw [hsum, hS0, mul_zero, map_zero]

end GlobalTheory.BI
