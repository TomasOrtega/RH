import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `hS : {α : K | α ^ N = 1} = ((Polynomial.nthRootsFinset N (1 : K) : Finset K) : Set K)`. Use extensionality with `x`. Simplify using `[Polynomial.mem_nthRootsFinset hN]`. Introduce `β hβ`. Establish `hβ' : β ^ N = 1` using `hβ`.

Use `set S := Polynomial.nthRootsFinset N (1 : K) with hSdef`. Establish `hmem : ∀ x, x ∈ S ↔ x ^ N = 1` using `fun x => Polynomial.mem_nthRootsFinset hN 1`. Establish `h' : ∀ l : ℕ, ∑ α ∈ S, c α * star (θ α ^ l) = 0`. Introduce `l`. Use `h l` as an intermediate fact.

Rewrite `this` using `[hS, finsum_mem_coe_finset]`. Then use the resulting hypothesis. Establish `hpow : ∀ x : K, x ^ N = 1 → θ x ^ N = 1` using `fun x hx => by rw [← map_pow, hx, map_one]`. Establish `hunit : ∀ x : K, x ^ N = 1 → star (θ x) * θ x = 1`. Introduce `x hx`. Establish `h1 : ‖θ x‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (hpow x hx) hN.ne'`.

Use `Complex.conj_mul' (θ x)` as an intermediate fact. Rewrite `this` using `[h1]`. Simplify using `using this`. Establish `hne : ∀ x : K, x ^ N = 1 → x ≠ 0`. Introduce and unpack `x hx rfl`.

Rewrite `hx` using `[zero_pow hN.ne']`. Conclude with `zero_ne_one hx`. Establish `key : ∀ α ∈ S, ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l = if α = β then (N : ℂ) else 0`. Introduce `α hα`. Establish `hα'` using `(hmem α).1 hα`.

Use `split_ifs with hab`. Substitute `hab` using the available equality. Rewrite using `[mul_comm, hunit α hα']`. Simplify using the standard rewrite rules. Establish `hz : θ β * star (θ α) ≠ 1`.

Introduce `hz`. Apply `hab` to reduce the goal to its premises. Apply `hθ α β (hne α hα') (hne β hβ')` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[geom_sum_eq hz, mul_pow, ← star_pow, hpow β hβ', hpow α hα']`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l) = 0`. Simplify using `only [h', mul_zero, Finset.sum_const_zero]`. Establish `h2 : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l) = ∑ α ∈ S, c α * ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, star_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum` using `[h2, Finset.sum_congr rfl (fun α hα => by rw [key α hα])]`.

Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', (hmem β).2 hβ', if_true] at hsum`. Conclude with `(mul_eq_zero.1 hsum).resolve_right (Nat.cast_ne_zero.2 hN.ne')`.
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
Introduce `F _ _ θ hθ n hn c h`. Establish `hq : 1 < Nat.card F` using `Finite.one_lt_card`. Establish `hN : 0 < Nat.card F ^ n - 1` using `Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)`. Conclude with `eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h`.
-/
theorem torus_fourier_injective : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → ∀ c : AlgebraicClosure F → ℂ, (∀ l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α * star (θ α ^ l) = 0) → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α = 0 := by
  intro F _ _ θ hθ n hn c h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hN : 0 < Nat.card F ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)
  exact eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h

end GlobalTheory.CuspGL
