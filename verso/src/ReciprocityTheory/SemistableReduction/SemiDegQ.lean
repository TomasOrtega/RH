import ReciprocityTheory.SemistableReduction.SemiDegN

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Introduce and unpack `_ ⟨y, ⟨_, hy⟩, rfl⟩ a ha`. Use `show (if (j : ℕ) ≤ a then y a else 0) = 0`. Use `split_ifs with h`. Conclude with `hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)`. Both sides reduce to the same expression.
-/
theorem gr_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if (j : ℕ) ≤ a then y a else 0) = 0
  split_ifs with h
  · exact hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
  · rfl

/- English proof (translation)
Take `⟨a, ha, hav⟩` from `hsp (Pi.single j 1)`. Establish `hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1)`. Introduce `i hi`. Establish `: i ≠ j` using `fun e => by rw [e] at hi; omega`. Simplify using `[this]`.

Use `⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0`. Rewrite using `[if_pos le_rfl]`. Simplify using `using ha`.
-/
theorem exists_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by
  obtain ⟨a, ha, hav⟩ := hsp (Pi.single j 1)
  have hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1) := by
    intro i hi
    have : i ≠ j := fun e => by rw [e] at hi; omega
    simp [this]
  refine ⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩
  show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0
  rw [if_pos le_rfl]
  simpa using ha

/- English proof (translation)
Introduce and unpack `_ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩`. Establish `hrev` using `Fin.val_rev j`. Establish `hj'` using `j.isLt`. Establish `e1 : projGe K r j x j = x j` using `by show (if (j : ℕ) ≤ j then x j else 0) = x j`. Rewrite using `[if_pos le_rfl]`.

Establish `e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j)` using `by show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _`. Rewrite using `[if_pos le_rfl]`. Rewrite using `[e1, e2]`. Establish `h` using `hint x hxL y hyL`. Rewrite `h` using `[formM_witt, Finset.sum_eq_single j]`.

Rewrite `h` using `[wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul]`. Then use the resulting hypothesis. Introduce `a _ ha`. Distinguish the cases in `hlt : (a : ℕ) < j`. Establish `hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m` using `Or.inl (by omega)`. Rewrite using `[wPart_outer r m a hao]`.

Establish `: y (Fin.rev a) = 0` using `hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)`. Rewrite using `[this, mul_zero, mul_zero]`. Establish `: x a = 0` using `hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)`. Rewrite using `[this, map_zero, zero_mul]`. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem pair_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have hrev := Fin.val_rev j
  have hj' := j.isLt
  have e1 : projGe K r j x j = x j := by
    show (if (j : ℕ) ≤ j then x j else 0) = x j
    rw [if_pos le_rfl]
  have e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j) := by
    show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _
    rw [if_pos le_rfl]
  rw [e1, e2]
  have h := hint x hxL y hyL
  rw [formM_witt, Finset.sum_eq_single j] at h
  · rwa [wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul] at h
  · intro a _ ha
    by_cases hlt : (a : ℕ) < j
    · have hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl (by omega)
      rw [wPart_outer r m a hao]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
      rw [this, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Introduce and unpack `_ ⟨y, ⟨_, hy⟩, rfl⟩ a ha`. Use `show (if m ≤ (a : ℕ) then y a else 0) = 0`. Use `split_ifs with h`. Conclude with `hy a (by omega)`. Both sides reduce to the same expression.
-/
theorem mid_supp {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if m ≤ (a : ℕ) then y a else 0) = 0
  split_ifs with h
  · exact hy a (by omega)
  · rfl

/- English proof (translation)
Introduce and unpack `_ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩`. Establish `h` using `hint x hxL y hyL`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[formM_witt]`. Simplify using `only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `ha` using `a.isLt`. Use `show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0) else 0) = _`. Distinguish the cases in `hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r`. Establish `ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m)` using `by omega`.

Simplify using `only [if_pos hmid, if_pos hmid.1]`. Rewrite using `[wVal_mid r m g a ho, wPart_mid r m a ho]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hmid]`. Distinguish the cases in `hlt : (a : ℕ) < m`.

Establish `ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m` using `Or.inl hlt`. Rewrite using `[wPart_outer r m a ho]`. Establish `: y (Fin.rev a) = 0` using `hyc _ (by rw [Fin.val_rev]; omega)`. Rewrite using `[this, mul_zero, mul_zero]`. Establish `: x a = 0` using `hxc a (by omega)`.

Rewrite using `[this, map_zero, zero_mul]`.
-/
theorem mid_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have h := hint x hxL y hyL
  convert h using 1
  rw [formM_witt]
  simp only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then
      S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0)
      else 0) = _
  by_cases hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r
  · have ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) := by omega
    simp only [if_pos hmid, if_pos hmid.1]
    rw [wVal_mid r m g a ho, wPart_mid r m a ho]
    ring
  · rw [if_neg hmid]
    by_cases hlt : (a : ℕ) < m
    · have ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl hlt
      rw [wPart_outer r m a ho]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by omega)
      rw [this, map_zero, zero_mul]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
