import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Finset

namespace GlobalTheory.HaarWeight

/- English proof (translation)
Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem filter_lt_succ {p n : ℕ} (h : n < p) :
    (univ.filter fun b : Fin p => b.1 < n + 1) = insert ⟨n, h⟩ (univ.filter fun b : Fin p => b.1 < n) := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

/- English proof (translation)
Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, Fin.le_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem filter_le_eq {p : ℕ} (a : Fin p) :
    (univ.filter fun b : Fin p => b ≤ a) = univ.filter fun b : Fin p => b.1 < a.1 + 1 := by
  ext b
  simp only [mem_filter, mem_univ, true_and, Fin.le_def]
  omega

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ j _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk j hj`. Establish `hP1 : 1 ≤ ∏ b ∈ range (k + 1), T b` using `hN k (by omega)`. Establish `hQ` using `ih (by omega) (m k) (hm k)`. Establish `hnn : 0 ≤ (∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k` using `mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (hT k) _)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_add, Finset.prod_range_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a) * ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := mul_le_mul_of_nonneg_right hQ hnn`. Use `_ = (∏ a ∈ range (k + 1), ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range (k + 1), T a ^ m a := by`. Rewrite using `[Finset.prod_range_succ (fun a => ∏ b ∈ range (a + 1), T b), Finset.prod_range_succ (fun a => T a ^ m a)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem one_le_partial_lemma (T : ℕ → ℝ) (m : ℕ → ℕ) (M p : ℕ) (hT : ∀ a, 0 ≤ T a)
    (hN : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T b) (hm : ∀ a, m a ≤ M) :
    ∀ k ≤ p, ∀ j ≤ M, (∏ b ∈ range k, T b) ^ j ≤
      (∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a := by
  intro k
  induction k with
  | zero => intro _ j _; simp
  | succ k ih =>
    intro hk j hj
    have hP1 : 1 ≤ ∏ b ∈ range (k + 1), T b := hN k (by omega)
    have hQ := ih (by omega) (m k) (hm k)
    have hnn : 0 ≤ (∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (hT k) _)
    calc (∏ b ∈ range (k + 1), T b) ^ j ≤ (∏ b ∈ range (k + 1), T b) ^ (m k + M) :=
          pow_le_pow_right₀ hP1 (by have := hm k; omega)
      _ = (∏ b ∈ range k, T b) ^ m k * ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := by
          rw [pow_add, Finset.prod_range_succ]; ring
      _ ≤ ((∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a) *
            ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := mul_le_mul_of_nonneg_right hQ hnn
      _ = (∏ a ∈ range (k + 1), ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range (k + 1), T a ^ m a := by
          rw [Finset.prod_range_succ (fun a => ∏ b ∈ range (a + 1), T b),
            Finset.prod_range_succ (fun a => T a ^ m a)]
          ring

/- English proof (translation)
Set `T' : ℕ → ℝ` to `fun b => if h : b < p then T ⟨b, h⟩ else 1`. Set `m' : ℕ → ℕ` to `fun b => if h : b < p then m ⟨b, h⟩ else 0`. Establish `hT' : ∀ b, 0 ≤ T' b`. Introduce `b`. Simplify using `only [T']`.

Use `split_ifs`. Conclude with `hT _`. Evaluate the numerical expressions. Establish `hm' : ∀ b, m' b ≤ M`. Introduce `b`.

Simplify using `only [m']`. Use `split_ifs`. Conclude with `hm _`. Conclude with `Nat.zero_le _`. Establish `hTT : ∀ b : Fin p, T b = T' b` using `fun b => by simp [T', b.2]`.

Establish `hmm : ∀ b : Fin p, m b = m' b` using `fun b => by simp [m', b.2]`. Establish `hpre : ∀ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b = ∏ b ∈ range (a.1 + 1), T' b`. Introduce `a`. Establish `ha` using `a.2`. Rewrite using `[filter_le_eq, Finset.prod_filter]`.

Repeatedly rewrite using `[hTT]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => if i < a.1 + 1 then T' i else 1) p, ← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [mem_filter, mem_range]`.

Use linear arithmetic over natural numbers and integers. Establish `hN' : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T' b` using `fun a ha => (hpre ⟨a, ha⟩) ▸ hN ⟨a, ha⟩`. Establish `key` using `one_le_partial_lemma T' m' M p hT' hN' hm' p le_rfl 0 (Nat.zero_le _)`. Rewrite `key` using `[pow_zero]`. Establish `e1 : (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) = ∏ a ∈ range p, ∏ b ∈ range (a + 1), T' b`.

Rewrite using `[← Fin.prod_univ_eq_prod_range (fun i => ∏ b ∈ range (i + 1), T' b) p]`. Conclude with `Finset.prod_congr rfl fun a _ => hpre a`. Establish `e2 : (∏ a : Fin p, T a ^ m a) = ∏ a ∈ range p, T' a ^ m' a`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun i => T' i ^ m' i) p]`. Conclude with `Finset.prod_congr rfl fun a _ => by rw [hTT, hmm]`.

Rewrite using `[e1, e2]`. Conclude with `key`.
-/
theorem one_le_partial {p : ℕ} (T : Fin p → ℝ) (m : Fin p → ℕ) (M : ℕ)
    (hN : ∀ a : Fin p, 1 ≤ ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) (hT : ∀ a, 0 ≤ T a)
    (hm : ∀ a, m a ≤ M) :
    1 ≤ (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) ^ M * ∏ a, T a ^ m a := by
  classical
  let T' : ℕ → ℝ := fun b => if h : b < p then T ⟨b, h⟩ else 1
  let m' : ℕ → ℕ := fun b => if h : b < p then m ⟨b, h⟩ else 0
  have hT' : ∀ b, 0 ≤ T' b := by
    intro b
    simp only [T']
    split_ifs
    · exact hT _
    · norm_num
  have hm' : ∀ b, m' b ≤ M := by
    intro b
    simp only [m']
    split_ifs
    · exact hm _
    · exact Nat.zero_le _
  have hTT : ∀ b : Fin p, T b = T' b := fun b => by simp [T', b.2]
  have hmm : ∀ b : Fin p, m b = m' b := fun b => by simp [m', b.2]
  have hpre : ∀ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b =
      ∏ b ∈ range (a.1 + 1), T' b := by
    intro a
    have ha := a.2
    rw [filter_le_eq, Finset.prod_filter]
    simp_rw [hTT]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < a.1 + 1 then T' i else 1) p, ← Finset.prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hN' : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T' b := fun a ha => (hpre ⟨a, ha⟩) ▸ hN ⟨a, ha⟩
  have key := one_le_partial_lemma T' m' M p hT' hN' hm' p le_rfl 0 (Nat.zero_le _)
  rw [pow_zero] at key
  have e1 : (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) =
      ∏ a ∈ range p, ∏ b ∈ range (a + 1), T' b := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ b ∈ range (i + 1), T' b) p]
    exact Finset.prod_congr rfl fun a _ => hpre a
  have e2 : (∏ a : Fin p, T a ^ m a) = ∏ a ∈ range p, T' a ^ m' a := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => T' i ^ m' i) p]
    exact Finset.prod_congr rfl fun a _ => by rw [hTT, hmm]
  rw [e1, e2]
  exact key

/- English proof (translation)
Introduce `n hn`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hn' : n < c.length` using `by omega`.

Rewrite using `[filter_lt_succ hn', Finset.sum_insert (by simp), ih (by omega)]`. Establish `hs` using `c.sizeUpTo_succ' ⟨n, hn'⟩`. Establish `hle` using `c.sizeUpTo_le (n + 1)`. Establish `hpos` using `c.one_le_blocksFun ⟨n, hn'⟩`. Simplify using `only at hs`.

Rewrite `hle`, the goal using `[hs]`. Generalize the expression as in `c.sizeUpTo n = x at hle ⊢`. Generalize the expression as in `c.blocksFun ⟨n, hn'⟩ = y at hle hpos ⊢`. Establish `h1 : x ≤ 2 * r + 1` using `by omega`. Establish `h2 : 2 * (x + y) ≤ 2 * r + 1 + y` using `by omega`.

Establish `h3 : x + y ≤ 2 * r + 1` using `by omega`. Use `zify [h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_exponent {r : ℕ} (c : Composition (r + 1)) : ∀ n, n ≤ c.length →
    ∑ b ∈ univ.filter (fun b : Fin c.length => b.1 < n),
      (2 * r + 1 + c.blocksFun b - 2 * c.sizeUpTo (b.1 + 1)) * c.blocksFun b =
      c.sizeUpTo n * (2 * r + 1 - c.sizeUpTo n) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < c.length := by omega
    rw [filter_lt_succ hn', Finset.sum_insert (by simp), ih (by omega)]
    have hs := c.sizeUpTo_succ' ⟨n, hn'⟩
    have hle := c.sizeUpTo_le (n + 1)
    have hpos := c.one_le_blocksFun ⟨n, hn'⟩
    simp only at hs
    rw [hs] at hle ⊢
    generalize c.sizeUpTo n = x at hle ⊢
    generalize c.blocksFun ⟨n, hn'⟩ = y at hle hpos ⊢
    have h1 : x ≤ 2 * r + 1 := by omega
    have h2 : 2 * (x + y) ≤ 2 * r + 1 + y := by omega
    have h3 : x + y ≤ 2 * r + 1 := by omega
    zify [h1, h2, h3]
    ring

/- English proof (translation)
Establish `ha` using `a.2`. Establish `hsum` using `sum_exponent γ.1 (a.1 + 1) (by omega)`. Rewrite `hsum` using `[← filter_le_eq]`. Unfold `endIdx`. Establish `hrd : ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * γ.1.sizeUpTo (b.1 + 1)))⁻¹) ^ (2 * γ.1.blocksFun b) = (rd ^ (2 * (γ.1.sizeUpTo (a.1 + 1) * (2 * r + 1 - γ.1.sizeUpTo (a.1 + 1)))))⁻¹`.

Repeatedly rewrite using `[inv_pow, ← pow_mul]`. Rewrite using `[Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← hsum, Finset.mul_sum]`. Use `congr 2`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Establish `hmin : v (endMin γ a) ^ 2 = ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), v (γ.2 b) ^ (2 * γ.1.blocksFun b)`.

Unfold `endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry`. Rewrite using `[map_prod, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Establish `hsg : v (((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign (γ.1.blocksFun b) : ℤ) : E)) = 1`.

Rewrite using `[Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign]`. Use `push_cast`. Rewrite using `[map_pow]`. Establish `hm1 : v (-1) = 1`. Establish `h1 : v (-1) * v (-1) = 1` using `by rw [← map_mul, neg_one_mul, neg_neg, map_one]`.

Establish `h0 : 0 ≤ v (-1)` using `by first`. Consider the case `exact v.1.nonneg (-1)`. Consider the case `exact apply_nonneg v (-1)`. Consider the case `positivity`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[hm1, one_pow]`. Rewrite using `[hsg, one_mul, ← pow_mul, mul_comm]`. Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, hrd, hmin]`.
-/
theorem endMin_sq {E : Type} [Field E] {r : ℕ} (rd : ℝ) (γ : PN.Pts E r) (a : Fin γ.1.length)
    (v : InfinitePlace E) :
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2 =
      ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
        ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * endIdx γ b))⁻¹ * v (γ.2 b)) ^ (2 * γ.1.blocksFun b) := by
  have ha := a.2
  have hsum := sum_exponent γ.1 (a.1 + 1) (by omega)
  rw [← filter_le_eq] at hsum
  unfold endIdx
  have hrd : ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * γ.1.sizeUpTo (b.1 + 1)))⁻¹) ^ (2 * γ.1.blocksFun b) =
      (rd ^ (2 * (γ.1.sizeUpTo (a.1 + 1) * (2 * r + 1 - γ.1.sizeUpTo (a.1 + 1)))))⁻¹ := by
    simp_rw [inv_pow, ← pow_mul]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← hsum, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun b _ => by ring
  have hmin : v (endMin γ a) ^ 2 = ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      v (γ.2 b) ^ (2 * γ.1.blocksFun b) := by
    unfold endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [map_mul, map_pow]
    have hsg : v (((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign (γ.1.blocksFun b) : ℤ) : E)) = 1 := by
      rw [Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign]
      push_cast
      rw [map_pow]
      have hm1 : v (-1) = 1 := by
        have h1 : v (-1) * v (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        have h0 : 0 ≤ v (-1) := by
          first
            | exact v.1.nonneg (-1)
            | exact apply_nonneg v (-1)
            | positivity
        nlinarith
      rw [hm1, one_pow]
    rw [hsg, one_mul, ← pow_mul, mul_comm]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, hrd, hmin]

/- English proof (translation)
Introduce `E _ _ _ r k TT rd H γ hrd hN hD`. Establish `hw0 : ∀ (w : InfinitePlace E) (x : E), 0 ≤ w x` using `fun w x => by first`. Consider the case `exact w.1.nonneg x`. Consider the case `exact apply_nonneg w x`. Consider the case `positivity`.

Set `Tw : Fin γ.1.length → InfinitePlace E → ℝ` to `fun a w => (rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)`. Set `U : Fin γ.1.length → ℝ` to `fun a => ∏ w : InfinitePlace E, Tw a w ^ (2 * γ.1.blocksFun a)`. Set `mm : Fin γ.1.length → ℕ` to `fun a => 2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1`. Establish `hTw : ∀ a w, 0 ≤ Tw a w` using `fun a w => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)`. Establish `hU : ∀ a, 0 ≤ U a` using `fun a => Finset.prod_nonneg fun w _ => pow_nonneg (hTw a w) _`.

Establish `hNa : ∀ a, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b = ∏ w : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2`. Introduce `a`. Simplify using `only [U]`. Rewrite using `[Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun w _ => (endMin_sq rd γ a w).symm`.

Establish `hmM : ∀ a, mm a ≤ 6 * (2 * r + 2)`. Introduce `a`. Simplify using `only [mm]`. Establish `h1` using `γ.1.sizeUpTo_le (a.1 + 1)`. Establish `h2` using `γ.1.sizeUpTo_succ' a`.

Unfold `endIdx`. Use linear arithmetic over natural numbers and integers. Establish `key` using `one_le_partial U mm (6 * (2 * r + 2)) (fun a => by rw [hNa]; exact hN a) hU hmM`. Establish `hND : (∏ a : Fin γ.1.length, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b) = NDPt rd γ`. Unfold `NDPt`.

Conclude with `Finset.prod_congr rfl fun a _ => hNa a`. Rewrite `key` using `[hND]`. Establish `hNDnn : 0 ≤ NDPt rd γ` using `Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun w _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (pow_nonneg (hw0 _ _) _)`. Establish `hY : ∏ a, U a ^ mm a = ∏ w : InfinitePlace E, ∏ a : Fin γ.1.length, Tw a w ^ (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1))`. Simplify using `only [U, mm]`.

Repeatedly rewrite using `[← Finset.prod_pow, ← pow_mul]`. Rewrite using `[Finset.prod_comm]`. Establish `hn : nPt rd k TT γ = NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a`. Rewrite using `[hY]`. Unfold `nPt NGPt`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow]`. Establish `hG0 : 0 ≤ NGPt rd TT γ` using `Finset.prod_nonneg fun w _ => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)`. Establish `hYnn : 0 ≤ ∏ a, U a ^ mm a` using `Finset.prod_nonneg fun a _ => pow_nonneg (hU a) _`. Establish `h1 : 1 ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_pow_le_haar : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  intro E _ _ _ r k TT rd H γ hrd hN hD
  have hw0 : ∀ (w : InfinitePlace E) (x : E), 0 ≤ w x := fun w x => by
    first
      | exact w.1.nonneg x
      | exact apply_nonneg w x
      | positivity
  let Tw : Fin γ.1.length → InfinitePlace E → ℝ := fun a w =>
    (rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)
  let U : Fin γ.1.length → ℝ := fun a => ∏ w : InfinitePlace E, Tw a w ^ (2 * γ.1.blocksFun a)
  let mm : Fin γ.1.length → ℕ := fun a => 2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1
  have hTw : ∀ a w, 0 ≤ Tw a w := fun a w => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hU : ∀ a, 0 ≤ U a := fun a => Finset.prod_nonneg fun w _ => pow_nonneg (hTw a w) _
  have hNa : ∀ a, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b =
      ∏ w : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 := by
    intro a
    simp only [U]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun w _ => (endMin_sq rd γ a w).symm
  have hmM : ∀ a, mm a ≤ 6 * (2 * r + 2) := by
    intro a
    simp only [mm]
    have h1 := γ.1.sizeUpTo_le (a.1 + 1)
    have h2 := γ.1.sizeUpTo_succ' a
    unfold endIdx
    omega
  have key := one_le_partial U mm (6 * (2 * r + 2)) (fun a => by rw [hNa]; exact hN a) hU hmM
  have hND : (∏ a : Fin γ.1.length, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b) =
      NDPt rd γ := by
    unfold NDPt
    exact Finset.prod_congr rfl fun a _ => hNa a
  rw [hND] at key
  have hNDnn : 0 ≤ NDPt rd γ := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (pow_nonneg (hw0 _ _) _)
  have hY : ∏ a, U a ^ mm a = ∏ w : InfinitePlace E, ∏ a : Fin γ.1.length,
      Tw a w ^ (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1)) := by
    simp only [U, mm]
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
  have hn : nPt rd k TT γ = NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a := by
    rw [hY]
    unfold nPt NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hG0 : 0 ≤ NGPt rd TT γ := Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hYnn : 0 ≤ ∏ a, U a ^ mm a := Finset.prod_nonneg fun a _ => pow_nonneg (hU a) _
  have h1 : 1 ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
    calc 1 ≤ NDPt rd γ ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a := key
      _ ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNDnn hD _) hYnn
  rw [hn]
  calc NGPt rd TT γ ^ (k - 1) = NGPt rd TT γ ^ (k - 1) * 1 := (mul_one _).symm
    _ ≤ NGPt rd TT γ ^ (k - 1) * (H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hG0 _)
    _ = H ^ (6 * (2 * r + 2)) * (NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a) := by ring

end GlobalTheory.HaarWeight
