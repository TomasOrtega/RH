import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Use `set ω := θ ζ with hωdef`. Establish `hNe : N ≠ 0` using `hN.ne'`. Establish `: NeZero N` using `⟨hNe⟩`. Establish `hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ)`. Use extensionality with `α`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨i, hi, rfl⟩` from `hζ.eq_pow_of_pow_eq_one h`. Conclude with `⟨i, hi, rfl⟩`.

Introduce and unpack `⟨i, -, rfl⟩`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ)`. Introduce `i hi j hj h`. Simplify using `only [Finset.coe_range, Set.mem_Iio] at hi hj`.

Conclude with `hζ.pow_inj hi hj h`. Rewrite using `[hset, finsum_mem_image hinj, finsum_mem_coe_finset]`. Establish `hnorm : ‖ω‖ = 1` using `hω.norm'_eq_one hNe`. Establish `hω0 : ω ≠ 0`. Introduce `h`.

Rewrite `hnorm` using `[h, norm_zero]`. Conclude with `zero_ne_one hnorm`. Establish `hstar : star ω = ω⁻¹`. Rewrite using `[Complex.inv_eq_conj hnorm]`. Both sides reduce to the same expression.

Use `set u := ω ^ k * (ω ^ l)⁻¹ with hu`. Establish `hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i`. Introduce `i`. Rewrite using `[map_pow, star_pow, star_pow, hstar, hu]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl (fun i _ => hterm i)]`. Establish `hm : ∀ a, ω ^ a = ω ^ (a % N)`. Introduce `a`. Use `conv_lhs => rw [← Nat.mod_add_div a N]`. Rewrite using `[pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]`.

Establish `huN : u ^ N = 1`. Rewrite using `[hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul, hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]`. Use `split_ifs with hkl`. Establish `hu1 : u = 1`. Rewrite using `[hu, hm k, hm l, show k % N = l % N from hkl]`.

Conclude with `mul_inv_cancel₀ (pow_ne_zero _ hω0)`. Simplify using `[hu1]`. Establish `hu1 : u ≠ 1`. Introduce `h`. Establish `hkl' : ω ^ k = ω ^ l` using `(mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)`.

Apply `hkl` to reduce the goal to its premises. Conclude with `hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')`. Rewrite using `[geom_sum_eq hu1, huN, sub_self, zero_div]`.
-/
theorem finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by
  classical
  set ω := θ ζ with hωdef
  have hNe : N ≠ 0 := hN.ne'
  have : NeZero N := ⟨hNe⟩

  have hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ) := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one h
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hζ.pow_inj hi hj h
  rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one hNe
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hstar : star ω = ω⁻¹ := by
    rw [Complex.inv_eq_conj hnorm]
    rfl

  set u := ω ^ k * (ω ^ l)⁻¹ with hu
  have hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i := by
    intro i
    rw [map_pow, star_pow, star_pow, hstar, hu]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hm : ∀ a, ω ^ a = ω ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have huN : u ^ N = 1 := by
    rw [hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
      hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  split_ifs with hkl
  · have hu1 : u = 1 := by
      rw [hu, hm k, hm l, show k % N = l % N from hkl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      have hkl' : ω ^ k = ω ^ l := (mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)
      apply hkl
      exact hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')
    rw [geom_sum_eq hu1, huN, sub_self, zero_div]

/- English proof (translation)
Introduce `F _ _ θ hθ n hn`. Establish `hq : 1 < Nat.card F` using `Finite.one_lt_card`. Establish `hqF : ((Nat.card F : ℕ) : F) = 0`. Use `Fintype.ofFinite F` as an intermediate fact. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `FiniteField.cast_card_eq_zero F`. Use `set q := Nat.card F with hqdef`. Establish `hqn : 1 < q ^ n` using `Nat.one_lt_pow hn.ne' hq`. Use `set N := q ^ n - 1 with hNdef`. Establish `hN : 0 < N` using `by omega`.

Establish `hNF : (N : F) ≠ 0`. Introduce `h`. Establish `h1 : ((N + 1 : ℕ) : F) = 0`. Rewrite using `[show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']`. Rewrite `h1` using `[Nat.cast_add, h, zero_add, Nat.cast_one]`.

Conclude with `one_ne_zero h1`. Establish `: NeZero (N : F)` using `⟨hNF⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hN.ne'`. Establish `hω : IsPrimitiveRoot (θ ζ) N` using `⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩`.

Conclude with `⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩`.
-/
theorem torus_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  intro F _ _ θ hθ n hn
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  have : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩

end GlobalTheory.CuspGL
