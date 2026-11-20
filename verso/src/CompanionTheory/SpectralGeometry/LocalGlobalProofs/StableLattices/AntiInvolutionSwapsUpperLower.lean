import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Unitary

variable {E ι : Type} [Ring E] [Fintype ι]

/- English proof (translation)
Establish `h : x * y = ∑ k, x * P k * y`. Rewrite using `[← Finset.sum_mul, ← Finset.mul_sum, hP.sum, mul_one]`. Rewrite using `[h, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `hP.idem k`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem piece_mul_mul {P : ι → E} (hP : IsPieces P) (x y : E) (i j : ι) :
    P i * (x * y) * P j = ∑ k, (P i * x * P k) * (P k * y * P j) := by
  have h : x * y = ∑ k, x * P k * y := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum, mul_one]
  rw [h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hP.idem k
  calc P i * (x * P k * y) * P j = P i * x * P k * y * P j := by simp only [mul_assoc]
    _ = P i * x * (P k * P k) * y * P j := by rw [hk]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[piece_mul_mul hP]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge (wt k) (wt i) with h | h` into its components or cases. Rewrite using `[hx i k h, zero_mul]`.

Rewrite using `[hy k j (lt_of_lt_of_le hij h), mul_zero]`.
-/
theorem upper_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsUpper wt P x) (hy : IsUpper wt P y) : IsUpper wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt k) (wt i) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_lt_of_le hij h), mul_zero]

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[piece_mul_mul hP]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge (wt i) (wt k) with h | h` into its components or cases. Rewrite using `[hx i k h, zero_mul]`.

Rewrite using `[hy k j (lt_of_le_of_lt h hij), mul_zero]`.
-/
theorem lower_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsLower wt P x) (hy : IsLower wt P y) : IsLower wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt i) (wt k) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_le_of_lt h hij), mul_zero]

/- English proof (translation)
Rewrite using `[piece_mul_mul hP]`. Use `Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations. Break down `lt_trichotomy (wt i) (wt k) with h | h | h` into its components or cases. Rewrite using `[hx i k h, zero_mul]`. Conclude with `absurd (hw h).symm hk`.

Rewrite using `[hy k i h, mul_zero]`.
-/
theorem diag_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLower wt P x) (hy : IsLower wt P y) (i : ι) :
    P i * (x * y) * P i = (P i * x * P i) * (P i * y * P i) := by
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_trichotomy (wt i) (wt k) with h | h | h
  · rw [hx i k h, zero_mul]
  · exact absurd (hw h).symm hk
  · rw [hy k i h, mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨lower_mul hP hx.1 hy.1, fun i => by rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩`.
-/
theorem lowerUni_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLowerUni wt P x) (hy : IsLowerUni wt P y) : IsLowerUni wt P (x * y) :=
  ⟨lower_mul hP hx.1 hy.1, fun i => by
    rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩

/- English proof (translation)
Use `⟨hb', fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `diag_mul hP hw hb.1 hb' i`. Rewrite `h1` using `[h, mul_one, hP.idem, hb.2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lowerUni_of_inv {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by
  refine ⟨hb', fun i => ?_⟩
  have h1 := diag_mul hP hw hb.1 hb' i
  rw [h, mul_one, hP.idem, hb.2] at h1
  calc P i * b' * P i = P i * (P i * b' * P i) := by simp only [← mul_assoc, hP.idem]
    _ = P i := h1.symm

/- English proof (translation)
Establish `h : c = ∑ i, ∑ j, P i * c * P j`. Simplify using `only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]`. Rewrite using `[h, ← hP.sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `(Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)` and prove the remaining obligations.

Break down `lt_trichotomy (wt i) (wt j) with h | h | h` into its components or cases. Conclude with `hl.1 i j h`. Conclude with `absurd (hw h).symm hj`. Conclude with `hu i j h`.
-/
theorem eq_one_of_upper_lowerUni {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by
  have h : c = ∑ i, ∑ j, P i * c * P j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]
  rw [h, ← hP.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · exact hl.1 i j h
  · exact absurd (hw h).symm hj
  · exact hu i j h

section Anti

variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}

/- English proof (translation)
Rewrite using `[hmul, hmul, hst, hst, hrev, hrev, mul_assoc]`.
-/
theorem st_block (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by
  rw [hmul, hmul, hst, hst, hrev, hrev, mul_assoc]

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]`.
-/
theorem st_upper (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsUpper wt P x) : IsUpper wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[st_block hrev hmul hst, hx (rev j) (rev i) (hord i j hij), h0]`.
-/
theorem st_lower (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLower wt P x) : IsLower wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord i j hij), h0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨st_lower hrev hord hmul h0 hst hx.1, fun i => by rw [st_block hrev hmul hst, hx.2, hst, hrev]⟩`.
-/
theorem st_lowerUni (hrev : ∀ i, rev (rev i) = i)
    (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLowerUni wt P x) :
    IsLowerUni wt P (st x) :=
  ⟨st_lower hrev hord hmul h0 hst hx.1, fun i => by
    rw [st_block hrev hmul hst, hx.2, hst, hrev]⟩

end Anti

/- English proof (translation)
Introduce `E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'`. Establish `ha'U : IsUpper wt P a'` using `hU a a' haa' ha'a ha`. Establish `hb'Uni : IsLowerUni wt P b'` using `lowerUni_of_inv hP hw hb (hL b b' hbb' hb'b hb.1) hbb'`. Establish `ha2U : IsUpper wt P (st a')` using `st_upper hrev hord hmul h0 hst ha'U`. Establish `hstb : IsLowerUni wt P (st b)` using `st_lowerUni hrev hord hmul h0 hst hb`.

Establish `e1 : st a * st a' = 1` using `by rw [← hmul, ha'a, h1]`. Establish `e2 : st b' * st b = 1` using `by rw [← hmul, hbb', h1]`. Establish `e3 : st b * st b' = 1` using `by rw [← hmul, hb'b, h1]`. Establish `e4 : st a' * st b' = a * b`. Establish `h2 : st (a * b) * (st a' * st b') = 1`.

Rewrite using `[hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]`. Combine the equalities or inequalities in the displayed calculation. Establish `e5 : st a' = a * b * st b`. Rewrite using `[← e4, mul_assoc, e2, mul_one]`. Establish `e6 : a' * st a' = b * st b`.

Establish `h3 : a' * (a * b * st b) = (a' * a) * b * st b` using `by simp only [mul_assoc]`. Rewrite using `[e5, h3, ha'a, one_mul]`. Establish `hc : a' * st a' = 1` using `eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U) (e6 ▸ lowerUni_mul hP hw hb hstb)`. Establish `e7 : st a' = a`. Combine the equalities or inequalities in the displayed calculation.

Establish `e8 : st b' = b`. Establish `: a * st b' = a * b` using `by rw [← e4, e7]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `e1` using `[e7]`. Rewrite `e3` using `[e8]`.

Conclude with `⟨e1, e3⟩`.
-/
theorem st_mul_self_of_factor : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  intro E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'
  have ha'U : IsUpper wt P a' := hU a a' haa' ha'a ha
  have hb'Uni : IsLowerUni wt P b' := lowerUni_of_inv hP hw hb (hL b b' hbb' hb'b hb.1) hbb'
  have ha2U : IsUpper wt P (st a') := st_upper hrev hord hmul h0 hst ha'U
  have hstb : IsLowerUni wt P (st b) := st_lowerUni hrev hord hmul h0 hst hb

  have e1 : st a * st a' = 1 := by rw [← hmul, ha'a, h1]
  have e2 : st b' * st b = 1 := by rw [← hmul, hbb', h1]
  have e3 : st b * st b' = 1 := by rw [← hmul, hb'b, h1]

  have e4 : st a' * st b' = a * b := by
    have h2 : st (a * b) * (st a' * st b') = 1 := by
      rw [hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]
    calc st a' * st b' = (a * b) * st (a * b) * (st a' * st b') := by rw [hs', one_mul]
      _ = a * b := by rw [mul_assoc, h2, mul_one]
  have e5 : st a' = a * b * st b := by
    rw [← e4, mul_assoc, e2, mul_one]

  have e6 : a' * st a' = b * st b := by
    have h3 : a' * (a * b * st b) = (a' * a) * b * st b := by simp only [mul_assoc]
    rw [e5, h3, ha'a, one_mul]
  have hc : a' * st a' = 1 :=
    eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U)
      (e6 ▸ lowerUni_mul hP hw hb hstb)
  have e7 : st a' = a := by
    calc st a' = a * a' * st a' := by rw [haa', one_mul]
      _ = a := by rw [mul_assoc, hc, mul_one]
  have e8 : st b' = b := by
    have : a * st b' = a * b := by rw [← e4, e7]
    calc st b' = a' * a * st b' := by rw [ha'a, one_mul]
      _ = a' * a * b := by rw [mul_assoc, this, mul_assoc]
      _ = b := by rw [ha'a, one_mul]
  rw [e7] at e1
  rw [e8] at e3
  exact ⟨e1, e3⟩

end GlobalTheory.CompanionTheory.Iwahori.Unitary
