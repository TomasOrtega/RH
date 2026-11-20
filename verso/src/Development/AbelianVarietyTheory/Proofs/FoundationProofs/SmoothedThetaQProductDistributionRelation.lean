import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CthFacMultipliable
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

open scoped UpperHalfPlane MatrixGroups Manifold in
/- English proof (translation)
Establish `hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (Finset.range m)` using `fun i hi j hj h => hζ.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h`. Establish `himage : (Finset.range m).image (fun j : ℕ => ζ ^ j) = Polynomial.nthRootsFinset m (1 : ℂ)`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `z hz`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hz`.

Rewrite using `[Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Rewrite using `[hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]`. Rewrite using `[hζ.pow_sub_pow_eq_prod_sub_mul x y hm, ← himage, Finset.prod_image hinj]`.
-/
theorem _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (x y : ℂ) : ∏ j ∈ Finset.range m, (x - ζ ^ j * y) = x ^ m - y ^ m := by
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (Finset.range m) := fun i hi j hj h =>
    hζ.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have himage :
      (Finset.range m).image (fun j : ℕ => ζ ^ j) = Polynomial.nthRootsFinset m (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [hζ.pow_sub_pow_eq_prod_sub_mul x y hm, ← himage, Finset.prod_image hinj]

open scoped UpperHalfPlane MatrixGroups Manifold in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.Sieg.ee, ← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.Sieg.ee_nat_div_eq_pow (m j : ℕ) :
    _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m) = Complex.exp (2 * Real.pi * Complex.I / m) ^ j := by
  rw [_root_.GlobalTheory.Sieg.ee, ← Complex.exp_nat_mul]
  congr 1
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in
/- English proof (translation)
Establish `key : ∀ {ξ : ℂ}, IsPrimitiveRoot ξ m → ∀ (u : ℂ) (g : ℕ → ℂ), (∀ j, g j = ξ ^ j * u) → ∏ j ∈ Finset.range m, (1 - q ^ n * g j) = 1 - (q ^ m) ^ n * u ^ m`. Introduce `ξ hξ u g hg`. Establish `h` using `_root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hξ hm 1 (q ^ n * u)`. Rewrite `h` using `[one_pow]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `_root_.GlobalTheory.Sieg.cthFac`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, key hζ t _ (fun j => by ring), key hζ.inv t⁻¹ _ (fun j => by rw [mul_inv, inv_pow]; ring), key (hζ.pow_of_coprime c hc) (t ^ c) _ (fun j => by rw [mul_pow, ← pow_mul, ← p …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow {c m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m) (hc : Nat.Coprime c m) (q t : ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) n =
      _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) n := by
  have key : ∀ {ξ : ℂ}, IsPrimitiveRoot ξ m → ∀ (u : ℂ) (g : ℕ → ℂ), (∀ j, g j = ξ ^ j * u) →
      ∏ j ∈ Finset.range m, (1 - q ^ n * g j) = 1 - (q ^ m) ^ n * u ^ m := by
    intro ξ hξ u g hg
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hξ hm 1 (q ^ n * u)
    rw [one_pow] at h
    calc ∏ j ∈ Finset.range m, (1 - q ^ n * g j)
          = ∏ j ∈ Finset.range m, (1 - ξ ^ j * (q ^ n * u)) :=
          Finset.prod_congr rfl fun j _ => by rw [hg]; ring
      _ = _ := by rw [h]; ring
  unfold _root_.GlobalTheory.Sieg.cthFac
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_pow, key hζ t _ (fun j => by ring),
    key hζ.inv t⁻¹ _ (fun j => by rw [mul_inv, inv_pow]; ring),
    key (hζ.pow_of_coprime c hc) (t ^ c) _
      (fun j => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring),
    key (hζ.pow_of_coprime c hc).inv (t ^ c)⁻¹ _
      (fun j => by rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm c j, mul_inv]; ring)]
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in

/- English proof (translation)
Introduce `c m q t _ _ hm hc hq _ ht _`. Use `set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef`. Establish `hζ : IsPrimitiveRoot ζ m` using `Complex.isPrimitiveRoot_exp m hm.ne'`. Establish `hζ0 : ζ ≠ 0` using `Complex.exp_ne_zero _`. Simplify using `only [_root_.GlobalTheory.Sieg.ee_nat_div_eq_pow]`.

Rewrite using `[← hζdef]`. Establish `hA : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -t ^ m`. Establish `h` using `_root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t`. Simplify using `only [zero_pow hm.ne', zero_sub] at h`. Rewrite using `[← h]`.

Conclude with `Finset.prod_congr rfl fun j _ => by ring`. Establish `hB : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m`. Establish `h` using `_root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t`. Rewrite `h` using `[one_pow]`. Rewrite using `[← h]`.

Conclude with `Finset.prod_congr rfl fun j _ => by ring`. Establish `hC : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c`. Establish `h` using `_root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)`. Rewrite `h` using `[one_pow, ← pow_mul, mul_comm c m, pow_mul]`. Rewrite using `[← h]`.

Conclude with `Finset.prod_congr rfl fun j _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring`. Establish `hD : ∏ j ∈ Finset.range m, ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) (n + 1) = ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) (n + 1)`. Rewrite using `[← Multipliable.tprod_finsetProd fun j _ => _root_.GlobalTheory.Sieg.cthFac_multipliable c q _ hq (mul_ne_zero ht (pow_ne_zero _ hζ0))]`. Conclude with `tprod_congr fun n => _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow hζ hm hc q t (n + 1)`. Unfold `_root_.GlobalTheory.Sieg.cth`.

Simplify using `only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow, Finset.prod_const, Finset.card_range, hB, hC, hD]`. Rewrite using `[hA]`.
-/
theorem _root_.GlobalTheory.Sieg.prod_cth_mul_ee : ∀ (c m : ℕ) (q t : ℂ), 1 < c →
    Nat.Coprime c 6 → 0 < m → Nat.Coprime c m →
    ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) →
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cth c q (t * _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m)) =
      _root_.GlobalTheory.Sieg.cth c (q ^ m) (t ^ m) := by
  intro c m q t _ _ hm hc hq _ ht _
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  simp only [_root_.GlobalTheory.Sieg.ee_nat_div_eq_pow]
  rw [← hζdef]
  have hA : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    simp only [zero_pow hm.ne', zero_sub] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hB : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hC : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow, ← pow_mul, mul_comm c m, pow_mul] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring
  have hD : ∏ j ∈ Finset.range m, ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd fun j _ =>
      _root_.GlobalTheory.Sieg.cthFac_multipliable c q _ hq (mul_ne_zero ht (pow_ne_zero _ hζ0))]
    exact tprod_congr fun n => _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  unfold _root_.GlobalTheory.Sieg.cth
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, hB, hC, hD]
  rw [hA]

end GlobalTheory.Sieg
