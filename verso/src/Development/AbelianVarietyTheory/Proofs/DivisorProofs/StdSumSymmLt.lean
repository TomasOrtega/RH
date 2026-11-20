import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.PutNest

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem put_apply' {R : Type} [CommRing R] (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j = if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem stdSum_symm_lt {p₁ p₂ p : ℕ} (h : p₁ + p₂ = p) (r : Fin p) (hr : r.val < p₁) :
    (stdSum h).symm r = Sum.inl ⟨r.val, hr⟩ := by
  rw [Equiv.symm_apply_eq]; ext; simp

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem stdSum_symm_ge {p₁ p₂ p : ℕ} (h : p₁ + p₂ = p) (r : Fin p) (hr : p₁ ≤ r.val) :
    (stdSum h).symm r = Sum.inr ⟨r.val - p₁, by omega⟩ := by
  rw [Equiv.symm_apply_eq]; ext; simp; omega

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[put_apply', put_apply']`. Use `split_ifs with ha hb hb`. Rewrite using `[put_apply']`. Rewrite using `[dif_pos (by simp only; omega)]`.

Apply the tactic sequence `congr 1 <;> ext <;> simp <;> omega`. Rewrite using `[put_apply', dif_neg (by simp only; omega)]`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem part1 {R : Type} [CommRing R] (n m o o' o₁ o₂ p q : ℕ) (X : Matrix (Fin p) (Fin q) R)
    (h1 : o₁ + p ≤ m) (h2 : o₂ + q ≤ m) : put n o o' (put m o₁ o₂ X) = put n (o + o₁) (o' + o₂) X := by
  ext i j
  rw [put_apply', put_apply']
  split_ifs with ha hb hb
  · rw [put_apply']
    rw [dif_pos (by simp only; omega)]
    congr 1 <;> ext <;> simp <;> omega
  · rw [put_apply', dif_neg (by simp only; omega)]
  · exfalso; omega
  · rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, put_apply', put_apply', put_apply']`. Use `split_ifs with ha hb hc hc hb hc hc`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Rewrite using `[submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromRows_apply_inl, add_zero]`. Rewrite using `[submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromRows_apply_inr, zero_add]`. Use `congr 1`. Use `ext`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem part2 {R : Type} [CommRing R] (n o₁ o₂ p q p₁ p₂ : ℕ) (h : p₁ + p₂ = p) (X : Matrix (Fin p₁) (Fin q) R)
    (Y : Matrix (Fin p₂) (Fin q) R) :
    put n o₁ o₂ ((fromRows X Y).submatrix (stdSum h).symm id) = put n o₁ o₂ X + put n (o₁ + p₁) o₂ Y := by
  ext i j
  rw [Matrix.add_apply, put_apply', put_apply', put_apply']
  split_ifs with ha hb hc hc hb hc hc
  · exfalso; omega
  · rw [submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromRows_apply_inl, add_zero]
  · rw [submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromRows_apply_inr, zero_add]
    congr 1; ext; simp only; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, put_apply', put_apply', put_apply']`. Use `split_ifs with ha hb hc hc hb hc hc`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Rewrite using `[submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromCols_apply_inl, add_zero]`. Rewrite using `[submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromCols_apply_inr, zero_add]`. Use `congr 1`. Use `ext`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem part3 {R : Type} [CommRing R] (n o₁ o₂ p q p₁ p₂ : ℕ) (h : p₁ + p₂ = p) (X : Matrix (Fin q) (Fin p₁) R)
    (Y : Matrix (Fin q) (Fin p₂) R) :
    put n o₁ o₂ ((fromCols X Y).submatrix id (stdSum h).symm) = put n o₁ o₂ X + put n o₁ (o₂ + p₁) Y := by
  ext i j
  rw [Matrix.add_apply, put_apply', put_apply', put_apply']
  split_ifs with ha hb hc hc hb hc hc
  · exfalso; omega
  · rw [submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromCols_apply_inl, add_zero]
  · rw [submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromCols_apply_inr, zero_add]
    congr 1; ext; simp only; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · simp

/- English proof (translation)
Introduce `R _ n m o o' o₁ o₂ p q p₁ p₂` and use `⟨fun X h1 h2 => part1 n m o o' o₁ o₂ p q X h1 h2, fun h X Y => part2 n o₁ o₂ p q p₁ p₂ h X Y, fun h X Y => part3 n o₁ o₂ p q p₁ p₂ h X Y⟩`.
-/
theorem main : ∀ (R : Type) [CommRing R] (n m o o' o₁ o₂ p q p₁ p₂ : ℕ), (∀ X : Matrix (Fin p) (Fin q) R, o₁ + p ≤ m → o₂ + q ≤ m → put n o o' (put m o₁ o₂ X) = put n (o + o₁) (o' + o₂) X) ∧ (∀ (h : p₁ + p₂ = p) (X : Matrix (Fin p₁) (Fin q) R) (Y : Matrix (Fin p₂) (Fin q) R), put n o₁ o₂ ((fromRows X Y).submatrix (stdSum h).symm id) = put n o₁ o₂ X + put n (o₁ + p₁) o₂ Y) ∧ (∀ (h : p₁ + p₂ = p) (X : Matrix (Fin q) (Fin p₁) R) (Y : Matrix (Fin q) (Fin p₂) R), put n o₁ o₂ ((fromCols X Y).submatrix id (stdSum h).symm) = put n o₁ o₂ X + put n o₁ (o₂ + p₁) Y) :=
  fun R _ n m o o' o₁ o₂ p q p₁ p₂ =>
    ⟨fun X h1 h2 => part1 n m o o' o₁ o₂ p q X h1 h2, fun h X Y => part2 n o₁ o₂ p q p₁ p₂ h X Y,
      fun h X Y => part3 n o₁ o₂ p q p₁ p₂ h X Y⟩

end GlobalTheory.GamMul.PutNest
