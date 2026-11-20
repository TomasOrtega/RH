import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eq_zero_of_finsum_mul_star_pow_eq_zero {K : Type} [Field K] (θ : K →* ℂ)
    (hθ : ∀ x y : K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : 0 < N) (c : K → ℂ)
    (h : ∀ l : ℕ, ∑ᶠ α ∈ {α : K | α ^ N = 1}, c α * star (θ α ^ l) = 0) :
    ∀ α ∈ {α : K | α ^ N = 1}, c α = 0 := by
  classical
  have hS : {α : K | α ^ N = 1} = ((Polynomial.nthRootsFinset N (1 : K) : Finset K) : Set K) := by
    ext x
    simp [Polynomial.mem_nthRootsFinset hN]
  intro β hβ
  have hβ' : β ^ N = 1 := hβ
  set S := Polynomial.nthRootsFinset N (1 : K) with hSdef
  have hmem : ∀ x, x ∈ S ↔ x ^ N = 1 := fun x => Polynomial.mem_nthRootsFinset hN 1
  have h' : ∀ l : ℕ, ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    intro l
    have := h l
    rwa [hS, finsum_mem_coe_finset] at this
  have hpow : ∀ x : K, x ^ N = 1 → θ x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  have hunit : ∀ x : K, x ^ N = 1 → star (θ x) * θ x = 1 := by
    intro x hx
    have h1 : ‖θ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hpow x hx) hN.ne'
    have := Complex.conj_mul' (θ x)
    rw [h1] at this
    simpa using this
  have hne : ∀ x : K, x ^ N = 1 → x ≠ 0 := by
    rintro x hx rfl
    rw [zero_pow hN.ne'] at hx
    exact zero_ne_one hx
  have key : ∀ α ∈ S, ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l
      = if α = β then (N : ℂ) else 0 := by
    intro α hα
    have hα' := (hmem α).1 hα
    split_ifs with hab
    · subst hab
      rw [mul_comm, hunit α hα']
      simp
    · have hz : θ β * star (θ α) ≠ 1 := by
        intro hz
        apply hab
        apply hθ α β (hne α hα') (hne β hβ')
        calc θ α = (θ β * star (θ α)) * θ α := by rw [hz, one_mul]
          _ = θ β := by rw [mul_assoc, hunit α hα', mul_one]
      rw [geom_sum_eq hz, mul_pow, ← star_pow, hpow β hβ', hpow α hα']
      simp
  have hsum : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    simp only [h', mul_zero, Finset.sum_const_zero]
  have h2 : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l)
      = ∑ α ∈ S, c α * ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, star_pow]
    ring
  rw [h2, Finset.sum_congr rfl (fun α hα => by rw [key α hα])] at hsum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', (hmem β).2 hβ', if_true] at hsum
  exact (mul_eq_zero.1 hsum).resolve_right (Nat.cast_ne_zero.2 hN.ne')

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem torus_fourier_injective : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → ∀ c : AlgebraicClosure F → ℂ, (∀ l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α * star (θ α ^ l) = 0) → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α = 0 := by
  intro F _ _ θ hθ n hn c h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hN : 0 < Nat.card F ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)
  exact eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h

end GlobalTheory.CuspGL
