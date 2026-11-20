import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Establish `h : ∀ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) = ((i : ℕ) : ℤ) * (∑ j, l j) - n * (l i * ((i : ℕ) : ℤ)) - (∑ j : Fin n, l j * ((j : ℕ) : ℤ)) + (∑ j : Fin n, ((j : ℕ) : ℤ)) * l i`. Introduce `i`. Establish `e : ∀ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) = ((i : ℕ) : ℤ) * l j - l i * ((i : ℕ) : ℤ) - l j * ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) * l i`. Introduce `j`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma wtPos_expand (n : ℕ) (l : Fin n → ℤ) :
    ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      2 * (∑ i : Fin n, ((i : ℕ) : ℤ)) * (∑ i, l i) - 2 * n * ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  have h : ∀ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      ((i : ℕ) : ℤ) * (∑ j, l j) - n * (l i * ((i : ℕ) : ℤ)) - (∑ j : Fin n, l j * ((j : ℕ) : ℤ))
        + (∑ j : Fin n, ((j : ℕ) : ℤ)) * l i := by
    intro i
    have e : ∀ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
        ((i : ℕ) : ℤ) * l j - l i * ((i : ℕ) : ℤ) - l j * ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) * l i := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/- English proof (translation)
Break down `le_total i j with h | h` into its components or cases. Establish `h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ)` using `by exact_mod_cast h`. Establish `h2` using `hl h`. Conclude with `mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)`. Establish `h1 : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ)` using `by exact_mod_cast h`.

Establish `h2` using `hl h`. Conclude with `mul_nonneg (by linarith) (by linarith)`.
-/
private lemma wtPos_term {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) (i j : Fin n) :
    0 ≤ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  rcases le_total i j with h | h
  · have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg (by linarith) (by linarith)

/- English proof (translation)
Establish `hne : i ≠ j` using `fun h => hij (by rw [h])`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `h1 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ)` using `by exact_mod_cast h`. Establish `h2 : l j < l i` using `lt_of_le_of_ne (hl h.le) (Ne.symm hij)`. Conclude with `mul_pos_of_neg_of_neg (by linarith) (by linarith)`.

Establish `h1 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ)` using `by exact_mod_cast h`. Establish `h2 : l i < l j` using `lt_of_le_of_ne (hl h.le) hij`. Conclude with `mul_pos (by linarith) (by linarith)`.
-/
private lemma wtPos_term_pos {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) {i j : Fin n} (hij : l i ≠ l j) :
    0 < (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l j < l i := lt_of_le_of_ne (hl h.le) (Ne.symm hij)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l i < l j := lt_of_le_of_ne (hl h.le) hij
    exact mul_pos (by linarith) (by linarith)

/- English proof (translation)
Simplify using `only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]`.
-/
private lemma wtPos_sum (n : ℕ) (l : Fin n → ℤ) (c : ℤ) :
    ∑ i, l i * (c - ((i : ℕ) : ℤ)) = c * (∑ i, l i) - ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]

/- English proof (translation)
Introduce `n l hl hl0`. Use `set S : ℤ := ∑ i, l i with hS`. Use `set T : ℤ := ∑ i : Fin n, l i * ((i : ℕ) : ℤ) with hT`. Break down `lt_trichotomy S 0 with h | h | h` into its components or cases. Use `⟨-(|T| + 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[wtPos_sum, ← hS, ← hT]`. Establish `h1 : T ≤ |T|` using `le_abs_self T`. Establish `h2 : 0 ≤ |T|` using `abs_nonneg T`. Use the polynomial consequences of the given equalities and inequalities. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, l a ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hl0 (funext hc)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, l a ≠ l b := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `hs : S = n * l a`. Rewrite using `[hS, Finset.sum_congr rfl (fun i _ => (hc i).symm)]`. Simplify using the standard rewrite rules. Rewrite `hs` using `[h]`.

Establish `hn : (n : ℤ) ≠ 0`. Establish `: 0 < n` using `Fin.pos a`. Conclude with `this.ne'` after adjusting the coercions. Conclude with `ha ((mul_eq_zero.mp hs.symm).resolve_left hn)`. Establish `hpos : 0 < ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i)`.

Use `Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => wtPos_term hl i j) ⟨a, Finset.mem_univ a, ?_⟩` and prove the remaining obligations. Conclude with `Finset.sum_pos' (fun j _ => wtPos_term hl a j) ⟨b, Finset.mem_univ b, wtPos_term_pos hl hb⟩`. Rewrite `hpos` using `[wtPos_expand, ← hS, ← hT, h]`. Establish `hn : (0 : ℤ) ≤ n` using `Int.natCast_nonneg n`. Establish `hT0 : T < 0`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use polynomial arithmetic with `[mul_nonneg hn hc]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[wtPos_sum, ← hS, ← hT]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨|T| + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[wtPos_sum, ← hS, ← hT]`. Establish `h1 : T ≤ |T|` using `le_abs_self T`. Establish `h2 : 0 ≤ |T|` using `abs_nonneg T`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.Gal.Gen.wtPos_pf :
    UpperTheory.Gal.Gen.WtPos := by
  intro n l hl hl0
  set S : ℤ := ∑ i, l i with hS
  set T : ℤ := ∑ i : Fin n, l i * ((i : ℕ) : ℤ) with hT
  rcases lt_trichotomy S 0 with h | h | h
  · refine ⟨-(|T| + 1), ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
  ·
    obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hl0 (funext hc)
    obtain ⟨b, hb⟩ : ∃ b, l a ≠ l b := by
      by_contra hc
      push_neg at hc
      have hs : S = n * l a := by
        rw [hS, Finset.sum_congr rfl (fun i _ => (hc i).symm)]
        simp
      rw [h] at hs
      have hn : (n : ℤ) ≠ 0 := by
        have : 0 < n := Fin.pos a
        exact_mod_cast this.ne'
      exact ha ((mul_eq_zero.mp hs.symm).resolve_left hn)
    have hpos : 0 < ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => wtPos_term hl i j) ⟨a, Finset.mem_univ a, ?_⟩
      exact Finset.sum_pos' (fun j _ => wtPos_term hl a j) ⟨b, Finset.mem_univ b, wtPos_term_pos hl hb⟩
    rw [wtPos_expand, ← hS, ← hT, h] at hpos
    have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hT0 : T < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg hn hc]
    refine ⟨0, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    linarith
  · refine ⟨|T| + 1, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
