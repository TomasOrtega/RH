import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Entries

variable {R : Type} [CommRing R] {a : ℕ}

/- English proof (translation)
Simplify using `only [posM, Matrix.sum_apply, Matrix.single_apply]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨(i, j), h⟩]`. Simplify using the standard rewrite rules. Introduce `t _ ht`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Conclude with `ht (Subtype.ext (Prod.ext e1 e2))`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Apply `h` to reduce the goal to its premises. Use `t.2` as an intermediate fact. Rewrite using `[← e1, ← e2]`.

Conclude with `this`.
-/
theorem posM_block_entry {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i j =
      if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have := t.2
    rw [← e1, ← e2]
    exact this

/- English proof (translation)
Simplify using `only [posM, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `ht : ((t.1.2 : Fin a) : ℕ) = n` using `by have := t.2; omega`. Use extensionality with `i j`. Distinguish the cases in `hi : i = t.1.1`.

Substitute `hi` using the available equality. Rewrite using `[Matrix.single_mul_apply_same, h _ ht, Matrix.one_apply, Matrix.single_apply]`. Apply the tactic sequence `by_cases hj : t.1.2 = j <;> simp [hj]`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨e1, _⟩`.

Conclude with `hi e1.symm`.
-/
theorem posM_col_mul {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) (M : Matrix (Fin a) (Fin a) R)
    (h : ∀ k : Fin a, (k : ℕ) = n → ∀ j, M k j = (1 : Matrix (Fin a) (Fin a) R) k j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  ext i j
  by_cases hi : i = t.1.1
  · subst hi
    rw [Matrix.single_mul_apply_same, h _ ht, Matrix.one_apply, Matrix.single_apply]
    by_cases hj : t.1.2 = j <;> simp [hj]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, Matrix.single_apply, if_neg]
    rintro ⟨e1, _⟩
    exact hi e1.symm

/- English proof (translation)
Simplify using `only [posM, Matrix.sum_apply, Matrix.single_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `ht : ((t.1.2 : Fin a) : ℕ) = n` using `by have := t.2; omega`. Distinguish the cases in `h : (t.1.1 : ℕ) + 1 = n`.

Rewrite using `[if_pos h, Finset.sum_eq_single t.1]`. Simplify using the standard rewrite rules. Introduce `p _ hp`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`.

Conclude with `hp (Prod.ext e1.symm e2.symm)`. Introduce `hp`. Conclude with `absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) hp`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations.

Establish `hp2` using `(Finset.mem_filter.1 hp).2`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Apply `h` to reduce the goal to its premises. Rewrite using `[e1, ← ht, e2]`.

Conclude with `hp2.symm`.
-/
theorem sum_posM_col {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) :
    (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x p.1 p.2) =
      ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then x t else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  by_cases h : (t.1.1 : ℕ) + 1 = n
  · rw [if_pos h, Finset.sum_eq_single t.1]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact hp (Prod.ext e1.symm e2.symm)
    · intro hp
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) hp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 := (Finset.mem_filter.1 hp).2
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [e1, ← ht, e2]
    exact hp2.symm

end Entries

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `u _ hd hc g`. Establish `hu : u = 1`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hd]`. Simplify using `[hc i j (Nat.zero_le _) h, h]`.

Substitute `hu` using the available equality. Establish `hs : (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (1 : GL (Fin a) (Ad E)).val p.1 p.2) = 0`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `hp2` using `(Finset.mem_filter.1 hp).2`. Establish `: p.1 ≠ p.2` using `fun e => by rw [e] at hp2; omega`.

Simplify using `[this]`. Rewrite using `[hs, AddChar.map_zero_eq_one, one_mul, one_mul]`. Consider the case `succ n ih`. Introduce `u ht hd hc g`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Use `ih u ht hd (fun i j _ hij => ?_) g` and prove the remaining obligations. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `hc i j (by have : (i : ℕ) < j := h; omega) hij`. Conclude with `ht i j h`.

Use `set y : UnipotentBlockColumnIndex a n n → Ad E := fun t => u.val t.1.1 t.1.2 with hy`. Establish `hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, u.val k j = (1 : Matrix (Fin a) (Fin a) (Ad E)) k j`. Introduce `k hk j`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality.

Simplify using `[hd]`. Rewrite using `[Matrix.one_apply, if_neg h]`. Break down `lt_or_gt_of_ne h with h' | h'` into its components or cases. Conclude with `hc k j (by have : (k : ℕ) < j := h'; omega) h`. Conclude with `ht k j h'`.

Establish `hval : ∀ i j, ((blkU y)⁻¹ * u).val i j = u.val i j - posM Subtype.val y i j`. Introduce `i j`. Establish `e : ((blkU y)⁻¹ * u).val = (1 - posM Subtype.val y) * u.val` using `rfl`. Rewrite using `[e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply]`. Establish `hz : ∀ i j : Fin a, ¬ ((i : ℕ) < n ∧ (j : ℕ) = n) → posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) y i j = 0`.

Introduce `i j h`. Rewrite using `[posM_block_entry, dif_neg]`. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `h ⟨h1, by omega⟩`. Establish `e1` using `ih ((blkU y)⁻¹ * u) ?_ ?_ ?_ g`.

Establish `e2 : u * g = blkU y * (((blkU y)⁻¹ * u) * g)` using `by group`. Rewrite using `[e2, hf n (by omega), e1, ← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Simplify using `only [hval, Finset.sum_sub_distrib, sum_posM_col, dot, eLast]`. Establish `hd2 : (∑ t : UnipotentBlockColumnIndex a n n, algebraMap E (Ad E) (if (t.1.1 : ℕ) + 1 = n then 1 else 0) * y t) = ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then y t else 0`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hd2, add_sub_cancel]`. Introduce `i j hji`. Rewrite using `[hval, ht i j hji, hz i j, sub_zero]`.

Introduce and unpack `⟨h1, h2⟩`. Establish `: (j : ℕ) < i` using `hji`. Use linear arithmetic over natural numbers and integers. Introduce `j`. Rewrite using `[hval, hd, hz j j, sub_zero]`.

Introduce and unpack `⟨h1, h2⟩`. Use linear arithmetic over natural numbers and integers. Introduce `i j hj hij`. Rewrite using `[hval]`. Distinguish the cases in `hjn : (j : ℕ) = n`.

Distinguish the cases in `hin : (i : ℕ) < n`. Rewrite using `[posM_block_entry, dif_pos ⟨hin, by omega, by omega⟩, sub_eq_zero]`. Rewrite using `[hz i j (fun h => hin h.1), sub_zero]`. Conclude with `ht i j (by`. Establish `: (j : ℕ) < i`.

Establish `: (i : ℕ) ≠ j` using `fun e => hij (Fin.ext e)`. Use linear arithmetic over natural numbers and integers. Conclude with `this)`. Rewrite using `[hc i j (by omega) hij, hz i j (fun h => hjn h.2), sub_zero]`.
-/
theorem whittakerLaw_upperUnipotent_identityColumns (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) (n : ℕ) :
    ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) →
      (∀ i j : Fin a, n ≤ (j : ℕ) → i ≠ j → u.val i j = 0) →
      ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  induction n with
  | zero =>
    intro u _ hd hc g
    have hu : u = 1 := by
      apply Units.ext
      ext i j
      by_cases h : i = j
      · subst h; simp [hd]
      · simp [hc i j (Nat.zero_le _) h, h]
    subst hu
    have hs : (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (1 : GL (Fin a) (Ad E)).val p.1 p.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp2 := (Finset.mem_filter.1 hp).2
      have : p.1 ≠ p.2 := fun e => by rw [e] at hp2; omega
      simp [this]
    rw [hs, AddChar.map_zero_eq_one, one_mul, one_mul]
  | succ n ih =>
    intro u ht hd hc g
    by_cases hn : n = 0
    · subst hn
      refine ih u ht hd (fun i j _ hij => ?_) g
      rcases lt_or_gt_of_ne hij with h | h
      · exact hc i j (by have : (i : ℕ) < j := h; omega) hij
      · exact ht i j h
    set y : UnipotentBlockColumnIndex a n n → Ad E := fun t => u.val t.1.1 t.1.2 with hy
    have hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, u.val k j = (1 : Matrix (Fin a) (Fin a) (Ad E)) k j := by
      intro k hk j
      by_cases h : k = j
      · subst h; simp [hd]
      · rw [Matrix.one_apply, if_neg h]
        rcases lt_or_gt_of_ne h with h' | h'
        · exact hc k j (by have : (k : ℕ) < j := h'; omega) h
        · exact ht k j h'
    have hval : ∀ i j, ((blkU y)⁻¹ * u).val i j = u.val i j - posM Subtype.val y i j := by
      intro i j
      have e : ((blkU y)⁻¹ * u).val = (1 - posM Subtype.val y) * u.val := rfl
      rw [e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply]
    have hz : ∀ i j : Fin a, ¬ ((i : ℕ) < n ∧ (j : ℕ) = n) → posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) y i j = 0 := by
      intro i j h
      rw [posM_block_entry, dif_neg]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, by omega⟩
    have e1 := ih ((blkU y)⁻¹ * u) ?_ ?_ ?_ g
    · have e2 : u * g = blkU y * (((blkU y)⁻¹ * u) * g) := by group
      rw [e2, hf n (by omega), e1, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [hval, Finset.sum_sub_distrib, sum_posM_col, dot, eLast]
      have hd2 : (∑ t : UnipotentBlockColumnIndex a n n, algebraMap E (Ad E) (if (t.1.1 : ℕ) + 1 = n then 1 else 0) * y t) =
          ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then y t else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
      rw [hd2, add_sub_cancel]
    · intro i j hji
      rw [hval, ht i j hji, hz i j, sub_zero]
      rintro ⟨h1, h2⟩
      have : (j : ℕ) < i := hji
      omega
    · intro j
      rw [hval, hd, hz j j, sub_zero]
      rintro ⟨h1, h2⟩
      omega
    · intro i j hj hij
      rw [hval]
      by_cases hjn : (j : ℕ) = n
      · by_cases hin : (i : ℕ) < n
        · rw [posM_block_entry, dif_pos ⟨hin, by omega, by omega⟩, sub_eq_zero]
        · rw [hz i j (fun h => hin h.1), sub_zero]
          exact ht i j (by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
              omega
            exact this)
      · rw [hc i j (by omega) hij, hz i j (fun h => hjn h.2), sub_zero]

/- English proof (translation)
The claim follows from `whittakerLaw_upperUnipotent_identityColumns ψ f hf a u ht hd (fun _ j h => absurd j.2 (by omega)) g`.
-/
theorem tri_law (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Ad E)) (ht : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j : Fin a, u.val j j = 1) (g : GA E a) :
    f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g :=
  whittakerLaw_upperUnipotent_identityColumns ψ f hf a u ht hd (fun _ j h => absurd j.2 (by omega)) g

end GlobalTheory.CuspGeneric
