import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Simplify using `[midI]`.
-/
theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by simp [midI]

/- English proof (translation)
Unfold `midI`. Conclude with `Fin.succ_ne_zero _`.
-/
theorem midI_ne_zero (r : ℕ) (j : Fin r) : midI r j ≠ 0 := by
  unfold midI
  exact Fin.succ_ne_zero _

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[midI_val, Fin.val_last]`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem midI_ne_last (r : ℕ) (j : Fin r) : midI r j ≠ Fin.last (r + 1) := by
  intro h
  have := congrArg Fin.val h
  rw [midI_val, Fin.val_last] at this
  have := j.isLt
  omega

/- English proof (translation)
Establish `h2` using `j.isLt`. Use `ext`. Simplify using `only [Fin.val_rev, midI_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem midI_rev (r : ℕ) (j : Fin r) : (midI r j).rev = midI r j.rev := by
  have h2 := j.isLt
  ext
  simp only [Fin.val_rev, midI_val]
  omega

/- English proof (translation)
Introduce `a b h`. Rewrite `h`, the goal using `[Fin.le_iff_val_le_val]`. Rewrite using `[midI_val, midI_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem midI_mono (r : ℕ) : Monotone (midI r) := by
  intro a b h
  rw [Fin.le_iff_val_le_val] at h ⊢
  rw [midI_val, midI_val]
  omega

/- English proof (translation)
Establish `hv` using `midI_val r j`. Establish `h2` using `j.isLt`. Unfold `midOf`. Use `split_ifs with h`. Conclude with `Option.some_inj.mpr (Fin.ext (by show (midI r j).val - 1 = j.val; omega))`.

Conclude with `absurd ⟨by omega, by omega⟩ h`.
-/
theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have h2 := j.isLt
  unfold midOf
  split_ifs with h
  · exact Option.some_inj.mpr (Fin.ext (by show (midI r j).val - 1 = j.val; omega))
  · exact absurd ⟨by omega, by omega⟩ h

/- English proof (translation)
Unfold `midOf`. Use `split_ifs with h`. Conclude with `absurd h.2 (by simp)`. Both sides reduce to the same expression.
-/
theorem midOf_last (r : ℕ) : midOf (Fin.last (r + 1)) = none := by
  unfold midOf
  split_ifs with h
  · exact absurd h.2 (by simp)
  · rfl

/- English proof (translation)
Distinguish the cases in `h0 : t.val = 0`. Use `left`. Conclude with `Fin.ext h0`. Distinguish the cases in `h1 : t.val = r + 1`. Use `right`.

Use `left`. Conclude with `Fin.ext h1`. Use `right`. Use `right`. Use `t.isLt` as an intermediate fact.

Use `⟨⟨t.val - 1, by omega⟩, Fin.ext ?_⟩` and prove the remaining obligations. Rewrite using `[midI_val]`. Use `show t.val = t.val - 1 + 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem fin_cases3 (r : ℕ) (t : Fin (r + 1 + 1)) : t = 0 ∨ t = Fin.last (r + 1) ∨ ∃ j, t = midI r j := by
  by_cases h0 : t.val = 0
  · left; exact Fin.ext h0
  · by_cases h1 : t.val = r + 1
    · right; left; exact Fin.ext h1
    · right; right
      have := t.isLt
      refine ⟨⟨t.val - 1, by omega⟩, Fin.ext ?_⟩
      rw [midI_val]
      show t.val = t.val - 1 + 1
      omega

/- English proof (translation)
Simplify using `[nuOf]`.
-/
theorem nuOf_last {m : ℕ} (mu : Fin (m + 1) → ℤ) : nuOf mu (Fin.last m) = 0 := by
  simp [nuOf]

/- English proof (translation)
Simplify using `only [wtPQ, if_neg (midI_ne_zero _ _), if_neg (midI_ne_last _ _)]`.
-/
theorem wtPQ_mid (mm a b : ℕ) (j : Fin mm) : wtPQ (mm + 1) a b (midI mm j) = 0 := by
  simp only [wtPQ, if_neg (midI_ne_zero _ _), if_neg (midI_ne_last _ _)]

/- English proof (translation)
Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`. Simplify using `only [nuOf, wtPQ, if_pos rfl, if_neg hne, if_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_wt_zero (mm a b : ℕ) : nuOf (wtPQ (mm + 1) a b) 0 = a + b := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [nuOf, wtPQ, if_pos rfl, if_neg hne, if_true]
  omega

/- English proof (translation)
Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`. Simplify using `only [nuOf]`. Rewrite using `[wtPQ_mid]`. Simplify using `only [wtPQ, if_neg hne, if_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_wt_mid (mm a b : ℕ) (j : Fin mm) : nuOf (wtPQ (mm + 1) a b) (midI mm j) = b := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [nuOf]
  rw [wtPQ_mid]
  simp only [wtPQ, if_neg hne, if_true]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`. Simplify using `only [Pi.add_apply, nuOf, wtPQ, if_neg hne, if_pos rfl]`. Apply the tactic sequence `split_ifs <;> push_cast <;> omega`.
-/
theorem nuOf_wt_add (mm a b a' b' : ℕ) :
    nuOf (wtPQ (mm + 1) (a + a') (b + b')) = nuOf (wtPQ (mm + 1) a b) + nuOf (wtPQ (mm + 1) a' b') := by
  funext t
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [Pi.add_apply, nuOf, wtPQ, if_neg hne, if_pos rfl]
  split_ifs <;> push_cast <;> omega

section Data

variable (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
  (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
  (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl)

include hmid in
/- English proof (translation)
Establish `hv` using `midI_val mm j`. Establish `h2` using `j.isLt`. Conclude with `abs_le.mp (hmid _ (by omega) (by omega))`.
-/
theorem lam_mid_bd (j : Fin mm) : -(ccl : ℤ) ≤ lam (midI mm j) ∧ lam (midI mm j) ≤ ccl := by
  have hv := midI_val mm j
  have h2 := j.isLt
  exact abs_le.mp (hmid _ (by omega) (by omega))

include h0 hl in
/- English proof (translation)
Simplify using `only [Pi.sub_apply, wtPQ, ↓reduceIte, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lo_zero : (lam - wtPQ (mm + 1) P Q) 0 = ccl := by
  simp only [Pi.sub_apply, wtPQ, ↓reduceIte, h0]
  ring

include h0 hl in
/- English proof (translation)
Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`. Simplify using `only [Pi.sub_apply, wtPQ, if_neg hne, ↓reduceIte, hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lo_last : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [Pi.sub_apply, wtPQ, if_neg hne, ↓reduceIte, hl]
  ring

include h0 hl in
/- English proof (translation)
Simplify using `only [Pi.sub_apply, wtPQ_mid, sub_zero]`.
-/
theorem lo_mid (j : Fin mm) : (lam - wtPQ (mm + 1) P Q) (midI mm j) = lam (midI mm j) := by
  simp only [Pi.sub_apply, wtPQ_mid, sub_zero]

include h0 hl in
/- English proof (translation)
Simplify using `only [nuOf, h0, hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lam_zero : nuOf lam 0 = P + Q + 2 * ccl := by
  simp only [nuOf, h0, hl]
  omega

include hl hmid in
/- English proof (translation)
Establish `hb` using `lam_mid_bd mm ccl lam hmid j`. Simplify using `only [nuOf, hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lam_mid (j : Fin mm) : ((nuOf lam (midI mm j) : ℕ) : ℤ) = lam (midI mm j) + Q + ccl := by
  have hb := lam_mid_bd mm ccl lam hmid j
  simp only [nuOf, hl]
  omega

include h0 hl in
/- English proof (translation)
Unfold `nuOf`. Rewrite using `[lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lo_zero : nuOf (lam - wtPQ (mm + 1) P Q) 0 = 2 * ccl := by
  unfold nuOf
  rw [lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl hmid in
/- English proof (translation)
Use `lam_mid_bd mm ccl lam hmid j` as an intermediate fact. Unfold `nuOf`. Rewrite using `[lo_mid mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lo_mid (j : Fin mm) :
    ((nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) : ℕ) : ℤ) = lam (midI mm j) + ccl := by
  have := lam_mid_bd mm ccl lam hmid j
  unfold nuOf
  rw [lo_mid mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl in
/- English proof (translation)
Simplify using `only [nuOf, dualWt, Fin.rev_zero, Fin.rev_last]`. Rewrite using `[lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lo'_zero : nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = 2 * ccl := by
  simp only [nuOf, dualWt, Fin.rev_zero, Fin.rev_last]
  rw [lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl hmid in
/- English proof (translation)
Establish `hb` using `lam_mid_bd mm ccl lam hmid j.rev`. Simplify using `only [nuOf, dualWt, Fin.rev_last]`. Rewrite using `[midI_rev, lo_mid mm ccl P Q lam h0 hl j.rev, lo_zero mm ccl P Q lam h0 hl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuOf_lo'_mid (j : Fin mm) :
    ((nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) : ℕ) : ℤ) = ccl - lam (midI mm j.rev) := by
  have hb := lam_mid_bd mm ccl lam hmid j.rev
  simp only [nuOf, dualWt, Fin.rev_last]
  rw [midI_rev, lo_mid mm ccl P Q lam h0 hl j.rev, lo_zero mm ccl P Q lam h0 hl]
  omega

include h0 hl in
/- English proof (translation)
Use function extensionality and compare the values at `t`. Break down `fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩` into its components or cases. Simplify using `only [shapeC, ↓reduceIte]`. Rewrite using `[nuOf_lo_zero mm ccl P Q lam h0 hl]`. Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`.

Simplify using `only [shapeC, if_neg hne, midOf_last]`. Rewrite using `[nuOf_last]`. Simplify using `only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]`.
-/
theorem shapeC_lo : shapeC (2 * ccl) (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) =
    nuOf (lam - wtPQ (mm + 1) P Q) := by
  funext t
  rcases fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩
  · simp only [shapeC, ↓reduceIte]
    rw [nuOf_lo_zero mm ccl P Q lam h0 hl]
  · have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
    simp only [shapeC, if_neg hne, midOf_last]
    rw [nuOf_last]
  · simp only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]

include h0 hl in
/- English proof (translation)
Use function extensionality and compare the values at `t`. Break down `fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩` into its components or cases. Simplify using `only [shapeC, ↓reduceIte]`. Rewrite using `[nuOf_lo'_zero mm ccl P Q lam h0 hl]`. Establish `hne : (Fin.last (mm + 1)) ≠ 0` using `by simp [Fin.ext_iff]`.

Simplify using `only [shapeC, if_neg hne, midOf_last]`. Rewrite using `[nuOf_last]`. Simplify using `only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]`.
-/
theorem shapeC_lo' : shapeC (2 * ccl) (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
    nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) := by
  funext t
  rcases fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩
  · simp only [shapeC, ↓reduceIte]
    rw [nuOf_lo'_zero mm ccl P Q lam h0 hl]
  · have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
    simp only [shapeC, if_neg hne, midOf_last]
    rw [nuOf_last]
  · simp only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]

end Data

/- English proof (translation)
Introduce `i j hij`. Conclude with `neg_le_neg (h (Fin.rev_le_rev.mpr hij))`.
-/
theorem qsDualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  exact neg_le_neg (h (Fin.rev_le_rev.mpr hij))

/- English proof (translation)
Simplify using `only [rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem rowDeg_add {k n : ℕ} (u v : Fin k × Fin n →₀ ℕ) (a : Fin k) : rowDeg (u + v) a = rowDeg u a + rowDeg v a := by
  simp only [rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_mul]`. Take `⟨x, hx, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hu`. Establish `h1 : coeff x.1 f ≠ 0` using `fun h => hne (by rw [h, zero_mul])`. Establish `h2 : coeff x.2 g ≠ 0` using `fun h => hne (by rw [h, mul_zero])`.

Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hf _ h1, hg _ h2]`.
-/
theorem rowA_mul {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f g : MvPolynomial (Fin k × Fin n) K) (d d' : ℕ)
    (hf : RowA a f d) (hg : RowA a g d') : RowA a (f * g) (d + d') := by
  classical
  intro u hu
  rw [coeff_mul] at hu
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have h1 : coeff x.1 f ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : coeff x.2 g ≠ 0 := fun h => hne (by rw [h, mul_zero])
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hf _ h1, hg _ h2]

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_map]`. Conclude with `hf u (fun h => hu (by rw [h, map_zero]))`.
-/
theorem rowA_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {k n : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin n) A) (d : ℕ) (hf : RowA a f d) : RowA a (map φ f) d := by
  intro u hu
  rw [coeff_map] at hu
  exact hf u (fun h => hu (by rw [h, map_zero]))

/- English proof (translation)
Introduce `u hu`. Simplify using `at hu`.
-/
private theorem rowA_zero_lemma {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (d : ℕ) :
    RowA a (0 : MvPolynomial (Fin k × Fin n) K) d := by
  intro u hu
  simp at hu

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_C]`. Use `split_ifs at hu with h`. Substitute `h` using the available equality. Simplify using `[rowDeg]`.

Conclude with `absurd rfl hu`.
-/
private theorem rowA_C_lemma_2 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (c : K) :
    RowA a (C c : MvPolynomial (Fin k × Fin n) K) 0 := by
  intro u hu
  rw [coeff_C] at hu
  split_ifs at hu with h
  · subst h
    simp [rowDeg]
  · exact absurd rfl hu

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_X']`. Use `split_ifs at hu with h`. Substitute `h` using the available equality. Take `⟨b, t⟩` from `v`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[rowDeg, Finsupp.single_apply, Prod.mk.injEq]`. Simplify using `[rowDeg, Finsupp.single_apply, Prod.mk.injEq, hb]`. Conclude with `absurd rfl hu`.
-/
private theorem rowA_X_lemma_3 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (v : Fin k × Fin n) :
    RowA a (X v : MvPolynomial (Fin k × Fin n) K) (if v.1 = a then 1 else 0) := by
  intro u hu
  rw [coeff_X'] at hu
  split_ifs at hu with h
  · subst h
    obtain ⟨b, t⟩ := v
    by_cases hb : b = a
    · subst hb
      simp [rowDeg, Finsupp.single_apply, Prod.mk.injEq]
    · simp [rowDeg, Finsupp.single_apply, Prod.mk.injEq, hb]
  · exact absurd rfl hu

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_add]`. Distinguish the cases in `h : coeff u f = 0`. Rewrite `hu` using `[h, zero_add]`. Conclude with `hg u hu`.

Conclude with `hf u h`.
-/
private theorem rowA_add_lemma_4 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k)
    (f g : MvPolynomial (Fin k × Fin n) K) (d : ℕ) (hf : RowA a f d) (hg : RowA a g d) :
    RowA a (f + g) d := by
  intro u hu
  rw [coeff_add] at hu
  by_cases h : coeff u f = 0
  · rw [h, zero_add] at hu
    exact hg u hu
  · exact hf u h

/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun g => RowA a g d) (fun g h hg hh => rowA_add_lemma_4 a g h d hg hh) (rowA_zero_lemma a d) hf`.
-/
private theorem rowA_sum_lemma_5 {K : Type} [CommRing K] {k n : ℕ} {ι : Type} (a : Fin k) (s : Finset ι)
    (f : ι → MvPolynomial (Fin k × Fin n) K) (d : ℕ) (hf : ∀ i ∈ s, RowA a (f i) d) :
    RowA a (∑ i ∈ s, f i) d :=
  Finset.sum_induction f (fun g => RowA a g d) (fun g h hg hh => rowA_add_lemma_4 a g h d hg hh)
    (rowA_zero_lemma a d) hf

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1`. Consider the case `cons i s hi ih`. Rewrite using `[Finset.prod_cons, Finset.sum_cons]`. Conclude with `rowA_mul a _ _ _ _ (hf i (Finset.mem_cons_self i s)) (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))`.
-/
private theorem rowA_prod_lemma_6 {K : Type} [CommRing K] {k n : ℕ} {ι : Type} (a : Fin k) (s : Finset ι)
    (f : ι → MvPolynomial (Fin k × Fin n) K) (d : ι → ℕ) (hf : ∀ i ∈ s, RowA a (f i) (d i)) :
    RowA a (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact rowA_mul a _ _ _ _ (hf i (Finset.mem_cons_self i s)) (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1`. Consider the case `succ m ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `rowA_mul a _ _ _ _ ih hf`.
-/
private theorem rowA_pow_lemma_7 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin n) K) (d m : ℕ) (hf : RowA a f d) : RowA a (f ^ m) (m * d) := by
  induction m with
  | zero => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact rowA_mul a _ _ _ _ ih hf

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[Matrix.det_apply']`. Apply `rowA_sum_lemma_5` to reduce the goal to its premises. Introduce `σ _`. Establish `hσ : (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) = 0 + ∑ i : Fin s, if Fin.castLE hr (σ i) = a then 1 else 0`.

Rewrite using `[zero_add]`. Conclude with `(Equiv.sum_comp σ (fun p => if Fin.castLE hr p = a then 1 else 0)).symm`. Rewrite using `[hσ]`. Apply `rowA_mul` to reduce the goal to its premises. Rewrite using `[← map_intCast (C : K →+* MvPolynomial (Fin k × Fin k) K)]`.

Conclude with `rowA_C_lemma_2 a _`. Apply `rowA_prod_lemma_6` to reduce the goal to its premises. Introduce `i _`. Conclude with `rowA_X_lemma_3 a _`.
-/
private theorem rowA_minor_lemma_8 (K : Type) [CommRing K] {k : ℕ} (a : Fin k) (s : ℕ) (hr hn : s ≤ k) :
    RowA a (lpMinor K s hr hn) (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply']
  apply rowA_sum_lemma_5
  intro σ _
  have hσ : (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) =
      0 + ∑ i : Fin s, if Fin.castLE hr (σ i) = a then 1 else 0 := by
    rw [zero_add]
    exact (Equiv.sum_comp σ (fun p => if Fin.castLE hr p = a then 1 else 0)).symm
  rw [hσ]
  apply rowA_mul
  · rw [← map_intCast (C : K →+* MvPolynomial (Fin k × Fin k) K)]
    exact rowA_C_lemma_2 a _
  · apply rowA_prod_lemma_6
    intro i _
    exact rowA_X_lemma_3 a _

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a.val, h⟩]`. Simplify using `[Fin.ext_iff]`. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `hc`. Apply `hb` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val hc` as an intermediate fact. Simplify using `using this`.

Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`. Establish `hp` using `p.isLt`. Rewrite using `[if_neg]`.

Introduce `hc`. Use `congrArg Fin.val hc` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
private theorem cnt_lemma_9 {k : ℕ} (a : Fin k) (s : ℕ) (hr : s ≤ k) :
    (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) = if a.val < s then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp [Fin.ext_iff]
    · intro b _ hb
      rw [if_neg]
      intro hc
      apply hb
      ext
      have := congrArg Fin.val hc
      simpa using this
    · simp
  · apply Finset.sum_eq_zero
    intro p _
    have hp := p.isLt
    rw [if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun n => if h : n < k then ν ⟨n, h⟩ else 0` from `⟨_, rfl⟩`. Establish `hgν : ∀ s : Fin k, ν s = g s.val` using `fun s => by simp [hg, s.isLt]`. Establish `hgn : ∀ s : Fin k, nuNext ν s = g (s.val + 1)` using `fun s => by simp only [nuNext, hg]`. Establish `hanti : ∀ m n, m ≤ n → g n ≤ g m`. Introduce `m n hmn`.

Simplify using `only [hg]`. Apply the tactic sequence `split_ifs <;> first | exact hν (Fin.mk_le_mk.mpr hmn) | omega | exact Nat.zero_le _`. Establish `key : ∀ n, n ≤ k → (∑ i ∈ Finset.range n, (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) = if a.val < n then g a.val - g n else 0`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `hn`. Rewrite using `[Finset.sum_range_succ, ih (by omega)]`.

Establish `h1` using `hanti n (n + 1) (by omega)`. Establish `h2` using `hanti a.val n`. Distinguish the cases in `ha : a.val < n`. Establish `h3` using `h2 (le_of_lt ha)`. Establish `ha' : a.val < n + 1` using `by omega`.

Simplify using `only [if_pos ha, if_pos ha']`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hb : a.val = n`. Establish `ha' : a.val < n + 1` using `by omega`. Simplify using `only [if_neg ha, if_pos ha']`.

Rewrite using `[hb]`. Use linear arithmetic over natural numbers and integers. Establish `ha' : ¬ a.val < n + 1` using `by omega`. Simplify using `only [if_neg ha, if_neg ha']`. Use linear arithmetic over natural numbers and integers.

Establish `hk` using `key k le_rfl`. Rewrite `hk` using `[if_pos a.isLt]`. Establish `hgk : g k = 0` using `by simp [hg]`. Rewrite `hk` using `[hgk, Nat.sub_zero]`. Rewrite using `[hgν a, ← hk, ← Fin.sum_univ_eq_sum_range (fun i => (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) k]`.

Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Use `show (g s.val - g (s.val + 1)) * _ = _`. Rewrite using `[hgν s, hgn s]`.
-/
private theorem tele_lemma_10 {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    ν a = ∑ s : Fin k, (ν s - nuNext ν s) * (if a.val < s.val + 1 then 1 else 0) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun n => if h : n < k then ν ⟨n, h⟩ else 0 := ⟨_, rfl⟩
  have hgν : ∀ s : Fin k, ν s = g s.val := fun s => by simp [hg, s.isLt]
  have hgn : ∀ s : Fin k, nuNext ν s = g (s.val + 1) := fun s => by simp only [nuNext, hg]
  have hanti : ∀ m n, m ≤ n → g n ≤ g m := by
    intro m n hmn
    simp only [hg]
    split_ifs <;> first | exact hν (Fin.mk_le_mk.mpr hmn) | omega | exact Nat.zero_le _
  have key : ∀ n, n ≤ k → (∑ i ∈ Finset.range n, (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) =
      if a.val < n then g a.val - g n else 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, ih (by omega)]
      have h1 := hanti n (n + 1) (by omega)
      have h2 := hanti a.val n
      by_cases ha : a.val < n
      · have h3 := h2 (le_of_lt ha)
        have ha' : a.val < n + 1 := by omega
        simp only [if_pos ha, if_pos ha']
        omega
      · by_cases hb : a.val = n
        · have ha' : a.val < n + 1 := by omega
          simp only [if_neg ha, if_pos ha']
          rw [hb]
          omega
        · have ha' : ¬ a.val < n + 1 := by omega
          simp only [if_neg ha, if_neg ha']
          omega
  have hk := key k le_rfl
  rw [if_pos a.isLt] at hk
  have hgk : g k = 0 := by simp [hg]
  rw [hgk, Nat.sub_zero] at hk
  rw [hgν a, ← hk, ← Fin.sum_univ_eq_sum_range (fun i => (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) k]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  show (g s.val - g (s.val + 1)) * _ = _
  rw [hgν s, hgn s]

/- English proof (translation)
Rewrite using `[tele_lemma_10 ν hν a]`. Unfold `hw`. Apply `rowA_prod_lemma_6` to reduce the goal to its premises. Introduce `s _`. Establish `hm` using `rowA_minor_lemma_8 K a (s.val + 1) s.isLt s.isLt`.

Rewrite `hm` using `[cnt_lemma_9]`. Conclude with `rowA_pow_lemma_7 a _ _ _ hm`.
-/
theorem rowA_hw (K : Type) [CommRing K] (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    RowA a (hw K (le_refl k) ν) (ν a) := by
  rw [tele_lemma_10 ν hν a]
  unfold hw
  apply rowA_prod_lemma_6
  intro s _
  have hm := rowA_minor_lemma_8 K a (s.val + 1) s.isLt s.isLt
  rw [cnt_lemma_9] at hm
  exact rowA_pow_lemma_7 a _ _ _ hm

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[hC]`. Take `⟨x, hx, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hu`. Establish `h1 : coeff x.1 (subY K r v) ≠ 0` using `fun h => hne (by rw [h, map_zero, zero_mul, map_zero])`. Establish `h2 : coeff x.2 (subY K r t) ≠ 0` using `fun h => hne (by rw [h, map_zero, mul_zero, map_zero])`.

Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hR K r a d v hv _ h1, hR K r a d' t ht _ h2]`.
-/
theorem rowA_lam (hC : LamCoeffP) (hR : SubRowP) (K : Type) [Field K] (r : ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (a : Fin (r + 1 + 1))
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (d d' : ℕ) (hv : RowA a v d) (ht : RowA a t d') :
    RowA a (lamOf K r L (blockEmb K true v * blockEmb K false t)) (d + d') := by
  classical
  intro u hu
  rw [hC] at hu
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have h1 : coeff x.1 (subY K r v) ≠ 0 := fun h => hne (by rw [h, map_zero, zero_mul, map_zero])
  have h2 : coeff x.2 (subY K r t) ≠ 0 := fun h => hne (by rw [h, map_zero, mul_zero, map_zero])
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hR K r a d v hv _ h1, hR K r a d' t ht _ h2]

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, map_X, eval_X, hp]`.

Unfold `idPoint`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem evalId_map {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (k n : ℕ) (h : MvPolynomial (Fin k × Fin n) A) :
    eval (idPoint B k n) (map ψ h) = ψ (eval (idPoint A k n) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X, hp]
    unfold idPoint
    split_ifs <;> simp

/- English proof (translation)
Unfold `detY`. Establish `h` using `RingHom.map_det (map φ) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))`. Use `h.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem detY_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) : map φ (detY A r) = detY B r := by
  unfold detY
  have h := RingHom.map_det (map φ) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine h.trans ?_
  congr 1
  ext i j
  simp

/- English proof (translation)
Unfold `resY`. Rewrite using `[map_mul, map_mul]`.
-/
theorem resY_mul (A : Type) [CommRing A] (r : ℕ) (s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    resY A r (s * t) = resY A r s * resY A r t := by
  unfold resY
  rw [map_mul, map_mul]

/- English proof (translation)
Simplify using `only [resY]`. Rewrite using `[hM A B φ r s]`. Conclude with `evalId_map (map φ) (r + 1 + 1) (r + 1 + 1) _`.
-/
theorem resY_map (hM : SubMapP) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) : resY B r (map φ s) = map φ (resY A r s) := by
  simp only [resY]
  rw [hM A B φ r s]
  exact evalId_map (map φ) (r + 1 + 1) (r + 1 + 1) _

end Formalism.MainNotions.flipOneThree.Pf

end
