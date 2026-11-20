import Mathlib

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set m' := m.updateRow p (Pi.single i 1) with hm'`. Establish `h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j`. Use `congrFun h1 j` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct]`. Rewrite `h2` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ p)]`. Establish `h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det`. Rewrite using `[Matrix.adjugate_apply, hm', Matrix.updateRow_idem]`. Establish `h4 : m'.mulVec x p = x i`.

Simplify using `[hm', Matrix.mulVec]`. Rewrite `h2` using `[h3, h4]`. Establish `h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I`. Use `I.sum_mem fun q hq => I.mul_mem_left _ ?_` and prove the remaining obligations. Establish `hq' : q ≠ p` using `Finset.ne_of_mem_erase hq`.

Establish `: m'.mulVec x q = m.mulVec x q`. Simplify using `[hm', Matrix.mulVec, Matrix.updateRow_ne hq']`. Rewrite using `[this]`. Conclude with `hm q hq'`. Use `h5 using 1` and compare the differences between its conclusion and the goal.

Take the linear combination `-h2`.
-/
theorem det_updateRow_single_mul_sub_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (i j : Fin g) :
    x j * (m.updateRow p (Pi.single i 1)).det - x i * (m.updateRow p (Pi.single j 1)).det ∈ I := by
  set m' := m.updateRow p (Pi.single i 1) with hm'
  have h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j := by
    have := congrFun h1 j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h2
  have h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det := by
    rw [Matrix.adjugate_apply, hm', Matrix.updateRow_idem]
  have h4 : m'.mulVec x p = x i := by
    simp [hm', Matrix.mulVec]
  rw [h3, h4] at h2
  have h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I := by
    refine I.sum_mem fun q hq => I.mul_mem_left _ ?_
    have hq' : q ≠ p := Finset.ne_of_mem_erase hq
    have : m'.mulVec x q = m.mulVec x q := by
      simp [hm', Matrix.mulVec, Matrix.updateRow_ne hq']
    rw [this]
    exact hm q hq'
  convert h5 using 1
  linear_combination -h2

/- English proof (translation)
Establish `h1 : (m.updateRow p (s.mulVec x)).det = ∑ ij : Fin g × Fin g, s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det)`. Establish `e : ∀ v : Fin g → T, (m.updateRow p v).det = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det`. Introduce `v`. Use `Matrix.cramer_transpose_apply m v p` as an intermediate fact. Rewrite using `[← this, Matrix.cramer_eq_adjugate_mulVec]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]`. Rewrite using `[e, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]`. Rewrite using `[h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Use `Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap` and prove the remaining obligations. Introduce and unpack `⟨i, j⟩`. Rewrite using `[← map_add, Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hji : s j i = - s i j`. Use `congrFun (congrFun hs i) j` as an intermediate fact. Simplify using `using this`. Use `I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Prod.fst_swap, Prod.snd_swap, hji]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨i, j⟩ h e`. Apply `h` to reduce the goal to its premises. Establish `: j = i` using `congrArg Prod.fst e`.

Substitute `this` using the available equality. Simplify using `[hd]`.
-/
theorem det_updateRow_alternating_mulVec_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add, Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]

/- English proof (translation)
Introduce `T _ g x hx c c' hc`. Use `set I := Ideal.span (Set.range (c.mulVec x)) with hI`. Set `M : Finset (Fin g) → Matrix (Fin g) (Fin g) T` to `fun S => Matrix.of fun i => if i ∈ S then c' i else c i`. Establish `hM : ∀ S q, (M S).mulVec x q = c.mulVec x q`. Introduce `S q`.

Distinguish the cases in `h : q ∈ S`. Rewrite using `[hc]`. Simplify using `[M, Matrix.mulVec, h]`. Simplify using `[M, Matrix.mulVec, h]`. Establish `key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Establish `: M ∅ = c` using `by ext i j; simp [M]`. Simplify using `[this]`.

Consider the case `insert p S hp ih`. Take `⟨s, hs, hd, hr⟩` from `hx (c p - c' p) (by`. Use `congrFun hc p` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`.

Conclude with `sub_eq_zero.mpr this)`. Establish `h1` using `det_updateRow_alternating_mulVec_mem x I (M S) p (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd`. Rewrite `h1` using `[← hr]`. Establish `e1 : (M S).updateRow p (c' p) = M (insert p S)`. Use extensionality with `i j`.

Distinguish the cases in `h : i = p`. Substitute `h` using the available equality. Simplify using `[M]`. Simplify using `[M, Matrix.updateRow_ne h, h]`. Establish `e2 : (M S).updateRow p (c p) = M S`.

Use extensionality with `i j`. Distinguish the cases in `h : i = p`. Substitute `h` using the available equality. Simplify using `[M, hp]`. Simplify using `[Matrix.updateRow_ne h]`.

Establish `e3` using `Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)`. Rewrite `e3` using `[sub_add_cancel, e1, e2]`. Use `I.add_mem ih h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `e3`.

Use `key Finset.univ` as an intermediate fact. Establish `e : M Finset.univ = c'` using `by ext i j; simp [M]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by
  intro T _ g x hx c c' hc
  set I := Ideal.span (Set.range (c.mulVec x)) with hI
  let M : Finset (Fin g) → Matrix (Fin g) (Fin g) T :=
    fun S => Matrix.of fun i => if i ∈ S then c' i else c i
  have hM : ∀ S q, (M S).mulVec x q = c.mulVec x q := by
    intro S q
    by_cases h : q ∈ S
    · rw [hc]; simp [M, Matrix.mulVec, h]
    · simp [M, Matrix.mulVec, h]
  have key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : M ∅ = c := by ext i j; simp [M]
      simp [this]
    | insert p S hp ih =>
      obtain ⟨s, hs, hd, hr⟩ := hx (c p - c' p) (by
        have := congrFun hc p
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr this)
      have h1 := det_updateRow_alternating_mulVec_mem x I (M S) p
        (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd
      rw [← hr] at h1
      have e1 : (M S).updateRow p (c' p) = M (insert p S) := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M]
        · simp [M, Matrix.updateRow_ne h, h]
      have e2 : (M S).updateRow p (c p) = M S := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M, hp]
        · simp [Matrix.updateRow_ne h]
      have e3 := Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)
      rw [sub_add_cancel, e1, e2] at e3
      have := I.add_mem ih h1
      convert this using 1
      linear_combination e3
  have := key Finset.univ
  have e : M Finset.univ = c' := by ext i j; simp [M]
  rwa [e] at this

end GlobalTheory
