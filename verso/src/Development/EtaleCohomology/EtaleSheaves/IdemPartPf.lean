import Development.EtaleCohomology.EtaleSheaves.HensCut

namespace LateralTheory.E.IdemPartPf

open Finset

/- English proof (translation)
Establish `hl : l ∈ (univ : Finset (Fin n)).erase m` using `mem_erase.2 ⟨hlm, mem_univ l⟩`. Rewrite using `[← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l), mul_prod_erase _ y (mem_univ l), h0, zero_mul]`.
-/
theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

/- English proof (translation)
Introduce `A _ n y h0 hu`. Take `⟨u, hu⟩` from `hu`. Set `e : Fin n → A` to `fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m`. Establish `horth : ∀ l m, l ≠ m → e l * e m = 0`. Introduce `l m hlm`.

Use `prod_erase_mul_prod_erase y h0 hlm` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [e]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [this, mul_zero]`.

Establish `hsum : ∑ l, e l = 1`. Simplify using `only [e]`. Rewrite using `[← mul_sum, ← hu, Units.inv_mul]`. Use `⟨e, ?_, horth, hsum, ?_⟩` and prove the remaining obligations. Introduce `l`.

Unfold `IsIdempotentElem`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_sum, sum_eq_single l]`. Introduce `m _ hml`. Conclude with `horth l m (Ne.symm hml)`.

Introduce `h`. Conclude with `absurd (mem_univ l) h`. Use `_ = e l := by rw [hsum, mul_one]`. Introduce `l`. Simplify using `only [e]`.

Rewrite using `[mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]`.
-/
theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
