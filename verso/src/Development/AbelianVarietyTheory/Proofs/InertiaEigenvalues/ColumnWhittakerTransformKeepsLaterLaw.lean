import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

noncomputable section

namespace GlobalTheory.CuspGeneric

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

/- English proof (translation)
Simplify using `only [posM, Matrix.sum_apply, Matrix.single_apply]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨(i, l), h⟩]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨⟨i', l'⟩, h'⟩ _ hne`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hne rfl`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Apply `h` to reduce the goal to its premises. Rewrite using `[← e1, ← e2]`. Conclude with `t.2`.
-/
theorem posM_blk_apply {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i l : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i l =
      if h : (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m then x ⟨(i, l), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, l), h⟩]
    · simp
    · rintro ⟨⟨i', l'⟩, h'⟩ _ hne
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [← e1, ← e2]
    exact t.2

/- English proof (translation)
Simplify using `only [posM, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _`.
-/
theorem posM_mul_posM_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a}
    {q : κ → Fin a × Fin a} (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) :
    posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

/- English proof (translation)
Rewrite `h` using `[Matrix.mul_apply]`. Take `⟨n, -, hn⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Simplify using `only [posM_blk_apply] at hn`. Use `split_ifs at hn with h1 h2`. Apply the tactic sequence `all_goals first`.

Consider the case `(refine ⟨?_, ?_, ?_⟩ <;> omega)`. Consider the case `simp at hn`.
-/
theorem blk_mul_support {j k : ℕ} (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) (i l : Fin a)
    (h : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
      posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) i l ≠ 0) :
    (i : ℕ) < j ∧ (l : ℕ) = k ∧ j < k := by
  rw [Matrix.mul_apply] at h
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [posM_blk_apply] at hn
  split_ifs at hn with h1 h2
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩ <;> omega)
    | simp at hn

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[posM_blk_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression. Assume the negation of the conclusion as `h'`.

Conclude with `h (hM i l fun e => h' e.symm)`.
-/
theorem posM_blk_of_support {r m : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l, M i l ≠ 0 → (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) (fun t => M t.1.1 t.1.2) = M := by
  ext i l
  rw [posM_blk_apply]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hM i l fun e => h' e.symm)

/- English proof (translation)
Establish `key : ∀ X Y Y' : Matrix (Fin a) (Fin a) R, Y' = Y + X * Y → Y' * X = 0 → (1 + X) * (1 + Y) = (1 + Y') * (1 + X)`. Introduce `X Y Y' h1 h2`. Establish `e : (1 + Y') * (1 + X) = 1 + X + Y' + Y' * X` using `by noncomm_ring`. Rewrite using `[e, h2, h1]`. Use `noncomm_ring`.

Apply `Units.ext` to reduce the goal to its premises. Use `key _ _ _ ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `posM _ (y + fun t : UnipotentBlockColumnIndex a k k => _) = _`. Rewrite using `[posM_add, posM_blk_of_support]`. Introduce `i l hne`.

Take `⟨h1, h2, h3⟩` from `blk_mul_support x y i l hne`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> omega`. Use `posM_mul_posM_eq_zero (fun s t e => ?_) _ _` and prove the remaining obligations. Establish `h1` using `s.2.2.1`. Establish `h2` using `t.2.1`.

Establish `h3` using `congrArg Fin.val e`. Use linear arithmetic over natural numbers and integers.
-/
theorem blkU_mul_blkU {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) * blkU y =
      blkU (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) * blkU x := by
  have key : ∀ X Y Y' : Matrix (Fin a) (Fin a) R, Y' = Y + X * Y → Y' * X = 0 →
      (1 + X) * (1 + Y) = (1 + Y') * (1 + X) := by
    intro X Y Y' h1 h2
    have e : (1 + Y') * (1 + X) = 1 + X + Y' + Y' * X := by noncomm_ring
    rw [e, h2, h1]
    noncomm_ring
  apply Units.ext
  refine key _ _ _ ?_ ?_
  · change posM _ (y + fun t : UnipotentBlockColumnIndex a k k => _) = _
    rw [posM_add, posM_blk_of_support]
    intro i l hne
    obtain ⟨h1, h2, h3⟩ := blk_mul_support x y i l hne
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · refine posM_mul_posM_eq_zero (fun s t e => ?_) _ _
    have h1 := s.2.2.1
    have h2 := t.2.1
    have h3 := congrArg Fin.val e
    omega

end Mat

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Establish `h0 : ∀ t : UnipotentBlockColumnIndex a k k, algebraMap E (Ad E) (eLast a k t) * (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0`. Introduce `t`. Unfold `eLast`. Use `split_ifs with h`. Establish `hz : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0`.

Assume the negation of the conclusion as `hne`. Use `(blk_mul_support x y _ _ hne).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hz, mul_zero]`. Simplify using the standard rewrite rules.

Simplify using `only [dot, mul_add, Finset.sum_add_distrib, h0, Finset.sum_const_zero, add_zero]`.
-/
theorem dot_eLast_shift {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → Ad E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) = dot (eLast a k) y := by
  have h0 : ∀ t : UnipotentBlockColumnIndex a k k, algebraMap E (Ad E) (eLast a k t) *
      (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
    intro t
    unfold eLast
    split_ifs with h
    · have hz : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
          posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
        by_contra hne
        have := (blk_mul_support x y _ _ hne).1
        omega
      rw [hz, mul_zero]
    · simp
  simp only [dot, mul_add, Finset.sum_add_distrib, h0, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Simplify using `only [colT, coefF]`. Rewrite using `[← avg_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast a k) y) * f (blkU x * g)`.

Rewrite using `[← mul_assoc, blkU_mul_blkU hk x y, mul_assoc, hf.law k hk, dot_eLast_shift hk x y]`. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colT_law_of_good (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ)
    (f : GA E a → ℂ) (hf : Good ψ (m + 1) f) (k : ℕ) (hk : m + 1 < k) (y : UnipotentBlockColumnIndex a k k → Ad E)
    (g : GA E a) : colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast a k) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hk x y, mul_assoc, hf.law k hk, dot_eLast_shift hk x y]
  rw [e1]
  ring

end GlobalTheory.CuspGeneric
