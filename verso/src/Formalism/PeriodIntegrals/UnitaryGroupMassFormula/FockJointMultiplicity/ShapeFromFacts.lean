import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory

noncomputable section

open Matrix FockH1Action

namespace PI.WFJM.Shape

open PI.FJM

section Gen

variable {n : ℕ}

def αP (f : Fin n → ℚ) : Fin (nP f) → ℕ := fun i => ⌊f (Fin.castLE (nP_le_nW f) i)⌋₊

def αN (f : Fin n → ℚ) : Fin (nN f) → ℕ := fun i => ⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊

def lpos {m : ℕ} (α : Fin m → ℕ) : List ℤ := List.ofFn fun i => (α i : ℤ)

def lneg {m : ℕ} (α : Fin m → ℕ) : List ℤ := (List.ofFn fun i => -(α i : ℤ)).reverse

/- English proof (translation)
Simplify using `[lpos]`.
-/
theorem length_lpos {m : ℕ} (α : Fin m → ℕ) : (lpos α).length = m := by simp [lpos]

/- English proof (translation)
Simplify using `[lneg]`.
-/
theorem length_lneg {m : ℕ} (α : Fin m → ℕ) : (lneg α).length = m := by simp [lneg]

/- English proof (translation)
Unfold `nP`. Prove the components needed by the constructor for the conclusion. Introduce `hi`. Establish `hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => 0 < f j)`. Introduce `j hj`.

Rewrite `hj` using `[Finset.mem_Iic]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `hj.lt_or_eq with h | h` into its components or cases. Conclude with `hseg j i h hi`. Rewrite using `[h]`.

Conclude with `hi`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers. Introduce `hi`.

Assume the negation of the conclusion as `hn`. Establish `hsub : Finset.univ.filter (fun j => 0 < f j) ⊆ Finset.Iio i`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Rewrite using `[Finset.mem_Iio]`.

Assume the negation of the conclusion as `hji`. Use `push_neg at hji`. Break down `hji.lt_or_eq with h | h` into its components or cases. Conclude with `hn (hseg i j h hj)`. Rewrite `hn` using `[h]`.

Conclude with `hn hj`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin n) :
    0 < f i ↔ (i : ℕ) < nP f := by
  classical
  unfold nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => 0 < f j) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg j i h hi
      · rw [h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => 0 < f j) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg i j h hj)
      · rw [h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/- English proof (translation)
Unfold `nN`. Establish `hin` using `i.isLt`. Prove the components needed by the constructor for the conclusion. Introduce `hi`. Establish `hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j => f j < 0)`.

Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Ici]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `hj.lt_or_eq with h | h` into its components or cases. Conclude with `hseg i j h hi`.

Rewrite using `[← h]`. Conclude with `hi`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Ici]`. Use linear arithmetic over natural numbers and integers.

Introduce `hi`. Assume the negation of the conclusion as `hn`. Establish `hsub : Finset.univ.filter (fun j => f j < 0) ⊆ Finset.Ioi i`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`.

Rewrite using `[Finset.mem_Ioi]`. Assume the negation of the conclusion as `hji`. Use `push_neg at hji`. Break down `hji.lt_or_eq with h | h` into its components or cases. Conclude with `hn (hseg j i h hj)`.

Rewrite `hn` using `[← h]`. Conclude with `hn hj`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Ioi]`. Use linear arithmetic over natural numbers and integers.
-/
theorem neg_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin n) :
    f i < 0 ↔ n - nN f ≤ (i : ℕ) := by
  classical
  unfold nN
  have hin := i.isLt
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j => f j < 0) := by
      intro j hj
      rw [Finset.mem_Ici] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg i j h hi
      · rw [← h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => f j < 0) ⊆ Finset.Ioi i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Ioi]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg j i h hj)
      · rw [← h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    omega

/- English proof (translation)
Unfold `nP nN`. Establish `hdis : Finset.univ.filter (fun j => 0 < f j) ∩ Finset.univ.filter (fun j => f j < 0) = ∅`. Use extensionality with `j`. Simplify using `only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_lt]`. Introduce `h`.

Conclude with `h.le`. Establish `h1` using `Finset.card_union_add_card_inter (Finset.univ.filter (fun j => 0 < f j)) (Finset.univ.filter (fun j => f j < 0))`. Rewrite `h1` using `[hdis, Finset.card_empty, add_zero]`. Establish `h2` using `Finset.card_le_univ (Finset.univ.filter (fun j => 0 < f j) ∪ Finset.univ.filter (fun j => f j < 0))`. Rewrite `h2` using `[Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nP_add_nN_le (f : Fin n → ℚ) : nP f + nN f ≤ n := by
  classical
  unfold nP nN
  have hdis : Finset.univ.filter (fun j => 0 < f j) ∩ Finset.univ.filter (fun j => f j < 0) = ∅ := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, not_lt]
    intro h; exact h.le
  have h1 := Finset.card_union_add_card_inter (Finset.univ.filter (fun j => 0 < f j))
    (Finset.univ.filter (fun j => f j < 0))
  rw [hdis, Finset.card_empty, add_zero] at h1
  have h2 := Finset.card_le_univ (Finset.univ.filter (fun j => 0 < f j) ∪ Finset.univ.filter (fun j => f j < 0))
  rw [Fintype.card_fin] at h2
  omega

/- English proof (translation)
Establish `hz0 : 0 ≤ z`. Establish `: (0 : ℚ) ≤ z` using `by rw [hz]; exact hx`. Conclude with `this` after adjusting the coercions. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hz0`. Rewrite using `[← hz]`.

Use `push_cast`. Rewrite using `[Nat.floor_natCast]`.
-/
theorem natFloor_of_int (x : ℚ) (z : ℤ) (hz : (z : ℚ) = x) (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by rw [hz]; exact hx
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [← hz]
  push_cast
  rw [Nat.floor_natCast]

/- English proof (translation)
Unfold `pad`. Rewrite using `[List.getD_eq_getElem?_getD, List.getElem?_map]`. Use `split_ifs with h1 h2`. Rewrite using `[List.getElem?_append_left (by simp; omega), List.getElem?_append_left h1]`. Simplify using `[h1]`.

Rewrite using `[List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]`. Simplify using `[List.getElem?_replicate, show i - x.length < k by omega]`. Rewrite using `[List.getElem?_append_right (by simp; omega)]`. Simplify using `only [List.length_append, List.length_replicate]`. Rewrite using `[List.getD_eq_getElem?_getD]`.

Establish `: i - (x.length + k) = i - x.length - k` using `by omega`. Rewrite using `[this]`. Apply the tactic sequence `cases y[i - x.length - k]? <;> simp`.
-/
theorem getD_pad (x y : List ℤ) (k i : ℕ) : (pad x k y).getD i 0 =
    if h : i < x.length then ((x[i] : ℤ) : ℚ) else if i < x.length + k then 0
      else ((y.getD (i - x.length - k) 0 : ℤ) : ℚ) := by
  unfold pad
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left h1]
    simp [h1]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
    simp [List.getElem?_replicate, show i - x.length < k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate]
    rw [List.getD_eq_getElem?_getD]
    have : i - (x.length + k) = i - x.length - k := by omega
    rw [this]
    cases y[i - x.length - k]? <;> simp

/- English proof (translation)
Unfold `lneg`. Rewrite using `[List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using ht)]`. Simplify using `[show m - 1 - t < m by omega]`.
-/
theorem getD_lneg {m : ℕ} (α : Fin m → ℕ) (t : ℕ) (ht : t < m) :
    (lneg α).getD t 0 = -(α ⟨m - 1 - t, by omega⟩ : ℤ) := by
  unfold lneg
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using ht)]
  simp [show m - 1 - t < m by omega]

/- English proof (translation)
Establish `hAB` using `nP_add_nN_le f`. Establish `hi` using `i.isLt`. Simplify using `only [getD_pad, length_lpos, length_lneg]`. Use `split_ifs with h1 h2`. Establish `hpos : 0 < f i` using `(pos_iff f hp i).2 h1`.

Simplify using `only [lpos, List.getElem_ofFn, αP]`. Establish `hci : Fin.castLE (nP_le_nW f) ⟨(i : ℕ), h1⟩ = i` using `Fin.ext rfl`. Rewrite using `[hci]`. Use `push_cast`. Conclude with `(natFloor_of_int (f i) ⌊f i⌋ (hint i) hpos.le).symm`.

Establish `hnp : ¬ 0 < f i` using `fun h => h1 ((pos_iff f hp i).1 h)`. Establish `hnn : ¬ f i < 0` using `fun h => by have := (neg_iff f hn i).1 h; omega`. Combine the linear relations using `[not_lt.1 hnp, not_lt.1 hnn]`. Establish `hneg : f i < 0` using `(neg_iff f hn i).2 (by omega)`. Rewrite using `[getD_lneg _ _ (by omega)]`.

Simplify using `only [αN]`. Establish `hci : Fin.rev (Fin.castLE (nN_le f) ⟨nN f - 1 - (i - nP f - (n - nP f - nN f)), by omega⟩) = i` using `Fin.ext (by simp [Fin.val_rev]; omega)`. Rewrite using `[hci]`. Use `push_cast`. Use `natFloor_of_int (-f i) (-⌊f i⌋) (by push_cast; rw [hint i]) (by linarith)` as an intermediate fact.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_pad (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) :
    f i = (pad (lpos (αP f)) (n - (lpos (αP f)).length - (lneg (αN f)).length) (lneg (αN f))).getD i 0 := by
  have hAB := nP_add_nN_le f
  have hi := i.isLt
  simp only [getD_pad, length_lpos, length_lneg]
  split_ifs with h1 h2
  ·
    have hpos : 0 < f i := (pos_iff f hp i).2 h1
    simp only [lpos, List.getElem_ofFn, αP]
    have hci : Fin.castLE (nP_le_nW f) ⟨(i : ℕ), h1⟩ = i := Fin.ext rfl
    rw [hci]
    push_cast
    exact (natFloor_of_int (f i) ⌊f i⌋ (hint i) hpos.le).symm
  ·
    have hnp : ¬ 0 < f i := fun h => h1 ((pos_iff f hp i).1 h)
    have hnn : ¬ f i < 0 := fun h => by have := (neg_iff f hn i).1 h; omega
    linarith [not_lt.1 hnp, not_lt.1 hnn]
  ·
    have hneg : f i < 0 := (neg_iff f hn i).2 (by omega)
    rw [getD_lneg _ _ (by omega)]
    simp only [αN]
    have hci : Fin.rev (Fin.castLE (nN_le f) ⟨nN f - 1 - (i - nP f - (n - nP f - nN f)), by omega⟩) = i :=
      Fin.ext (by simp [Fin.val_rev]; omega)
    rw [hci]
    push_cast
    have := natFloor_of_int (-f i) (-⌊f i⌋) (by push_cast; rw [hint i]) (by linarith)
    rw [this]; ring

/- English proof (translation)
Establish `hpos : 0 < f (Fin.castLE (nP_le_nW f) i)` using `(pos_iff f hp _).2 (by simp)`. Use `natFloor_of_int _ _ (hint (Fin.castLE (nP_le_nW f) i)) hpos.le` as an intermediate fact. Unfold `αP`. Establish `h2 : (0 : ℚ) < ((⌊f (Fin.castLE (nP_le_nW f) i)⌋₊ : ℕ) : ℚ)` using `by rw [this]; exact hpos`. Conclude with `h2` after adjusting the coercions.
-/
theorem pos_of_αP (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin (nP f)) : 0 < αP f i := by
  have hpos : 0 < f (Fin.castLE (nP_le_nW f) i) := (pos_iff f hp _).2 (by simp)
  have := natFloor_of_int _ _ (hint (Fin.castLE (nP_le_nW f) i)) hpos.le
  unfold αP
  have h2 : (0 : ℚ) < ((⌊f (Fin.castLE (nP_le_nW f) i)⌋₊ : ℕ) : ℚ) := by rw [this]; exact hpos
  exact_mod_cast h2

/- English proof (translation)
Establish `hneg : f (Fin.rev (Fin.castLE (nN_le f) i)) < 0` using `(neg_iff f hn _).2 (by simp [Fin.val_rev]; omega)`. Use `natFloor_of_int (-f (Fin.rev (Fin.castLE (nN_le f) i))) (-⌊f (Fin.rev (Fin.castLE (nN_le f) i))⌋) (by push_cast; rw [hint]) (by linarith)` as an intermediate fact. Unfold `αN`. Establish `h2 : (0 : ℚ) < ((⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊ : ℕ) : ℚ)` using `by rw [this]; linarith`. Conclude with `h2` after adjusting the coercions.
-/
theorem pos_of_αN (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin (nN f)) : 0 < αN f i := by
  have hneg : f (Fin.rev (Fin.castLE (nN_le f) i)) < 0 :=
    (neg_iff f hn _).2 (by simp [Fin.val_rev]; omega)
  have := natFloor_of_int (-f (Fin.rev (Fin.castLE (nN_le f) i))) (-⌊f (Fin.rev (Fin.castLE (nN_le f) i))⌋)
    (by push_cast; rw [hint]) (by linarith)
  unfold αN
  have h2 : (0 : ℚ) < ((⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊ : ℕ) : ℚ) := by rw [this]; linarith
  exact_mod_cast h2

/- English proof (translation)
Take `⟨hmk, _, hd⟩` from `h`. Apply `List.ext_getElem (by simp [lpos, hmk])` to reduce the goal to its premises. Introduce `t h1 h2`. Simplify using `only [lpos, List.getElem_ofFn]`. Rewrite using `[hd ⟨t, by simpa [lpos] using h1⟩ ⟨t, by simpa [lpos] using h2⟩ rfl]`.
-/
theorem lpos_eq_of_sq {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lpos α = lpos β := by
  obtain ⟨hmk, _, hd⟩ := h
  apply List.ext_getElem (by simp [lpos, hmk])
  intro t h1 h2
  simp only [lpos, List.getElem_ofFn]
  rw [hd ⟨t, by simpa [lpos] using h1⟩ ⟨t, by simpa [lpos] using h2⟩ rfl]

/- English proof (translation)
Take `⟨hmk, _, hd⟩` from `h`. Unfold `lneg`. Use `congr 1`. Apply `List.ext_getElem (by simp [hmk])` to reduce the goal to its premises. Introduce `t h1 h2`.

Simplify using `only [List.getElem_ofFn]`. Rewrite using `[hd ⟨t, by simpa using h1⟩ ⟨t, by simpa using h2⟩ rfl]`.
-/
theorem lneg_eq_of_sq {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lneg α = lneg β := by
  obtain ⟨hmk, _, hd⟩ := h
  unfold lneg
  congr 1
  apply List.ext_getElem (by simp [hmk])
  intro t h1 h2
  simp only [List.getElem_ofFn]
  rw [hd ⟨t, by simpa using h1⟩ ⟨t, by simpa using h2⟩ rfl]

/- English proof (translation)
Unfold `lpos`. Rewrite using `[List.pairwise_ofFn]`. Introduce `i j hij`. Conclude with `h hij.le` after adjusting the coercions.
-/
theorem pairwise_lpos {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lpos α).Pairwise (· ≥ ·) := by
  unfold lpos
  rw [List.pairwise_ofFn]
  intro i j hij
  exact_mod_cast h hij.le

/- English proof (translation)
Unfold `lneg`. Rewrite using `[List.pairwise_reverse, List.pairwise_ofFn]`. Introduce `i j hij`. Establish `: α j ≤ α i` using `h hij.le`. Simplify using `only [ge_iff_le, neg_le_neg_iff]`.

Conclude with `this` after adjusting the coercions.
-/
theorem pairwise_lneg {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lneg α).Pairwise (· ≥ ·) := by
  unfold lneg
  rw [List.pairwise_reverse, List.pairwise_ofFn]
  intro i j hij
  have : α j ≤ α i := h hij.le
  simp only [ge_iff_le, neg_le_neg_iff]
  exact_mod_cast this

end Gen

end PI.WFJM.Shape

namespace PI.FJM

open PI.WFJM.Shape

/- English proof (translation)
Introduce `p q r s μ μ' hB hS hI`. Take `⟨hA, hBb, hC, hD⟩` from `hB`. Take `⟨s1, s2, s3, s4, s5, s6, s7, s8⟩` from `hS`. Take `⟨hI1, hI2⟩` from `hI`. Establish `iL1 : ∀ i, ((⌊leftWeightFirst p q r s μ i⌋ : ℤ) : ℚ) = leftWeightFirst p q r s μ i` using `fun i => hI1 (.inl i)`.

Establish `firstRealIndex : ∀ j, ((⌊leftWeightSecond p q r s μ j⌋ : ℤ) : ℚ) = leftWeightSecond p q r s μ j` using `fun j => hI1 (.inr j)`. Establish `iL2 : ∀ k, ((⌊rightWeightFirst p q r s μ' k⌋ : ℤ) : ℚ) = rightWeightFirst p q r s μ' k` using `fun k => hI2 (.inl k)`. Establish `secondRealIndex : ∀ l, ((⌊rightWeightSecond p q r s μ' l⌋ : ℤ) : ℚ) = rightWeightSecond p q r s μ' l` using `fun l => hI2 (.inr l)`. Establish `eA : lpos (αA p q r s μ) = lpos (αP (rightWeightFirst p q r s μ'))` using `lpos_eq_of_sq hA`. Establish `eB : lneg (αB p q r s μ) = lneg (αN (rightWeightSecond p q r s μ'))` using `lneg_eq_of_sq hBb`.

Establish `eC : lpos (αC p q r s μ) = lpos (αP (rightWeightSecond p q r s μ'))` using `lpos_eq_of_sq hC`. Establish `eD : lneg (αD p q r s μ) = lneg (αN (rightWeightFirst p q r s μ'))` using `lneg_eq_of_sq hD`. Establish `nA : nP (leftWeightFirst p q r s μ) = nP (rightWeightFirst p q r s μ')` using `hA.1`. Establish `nB : nN (leftWeightFirst p q r s μ) = nN (rightWeightSecond p q r s μ')` using `hBb.1`. Establish `nC : nP (leftWeightSecond p q r s μ) = nP (rightWeightSecond p q r s μ')` using `hC.1`.

Establish `nD : nN (leftWeightSecond p q r s μ) = nN (rightWeightFirst p q r s μ')` using `hD.1`. Use `⟨lpos (αA p q r s μ), lneg (αB p q r s μ), lpos (αC p q r s μ), lneg (αD p q r s μ), ?_, ?_, ?_, ?_, pairwise_lpos hA.2.1, pairwise_lneg hBb.2.1, pairwise_lpos hC.2.1, pairwise_lneg hD.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [lpos, List.mem_ofFn] at hv`. Take `⟨i, rfl⟩` from `hv`.

Conclude with `pos_of_αP (leftWeightFirst p q r s μ) iL1 s1 i` after adjusting the coercions. Introduce `v hv`. Simplify using `only [lpos, List.mem_ofFn] at hv`. Take `⟨i, rfl⟩` from `hv`. Conclude with `pos_of_αP (leftWeightSecond p q r s μ) firstRealIndex s3 i` after adjusting the coercions.

Introduce `v hv`. Simplify using `only [lneg, List.mem_reverse, List.mem_ofFn] at hv`. Take `⟨i, rfl⟩` from `hv`. Use `pos_of_αN (leftWeightFirst p q r s μ) iL1 s2 i` as an intermediate fact. Simplify using `only [Left.neg_neg_iff, Nat.cast_pos]`.

Conclude with `this`. Introduce `v hv`. Simplify using `only [lneg, List.mem_reverse, List.mem_ofFn] at hv`. Take `⟨i, rfl⟩` from `hv`. Use `pos_of_αN (leftWeightSecond p q r s μ) firstRealIndex s4 i` as an intermediate fact.

Simplify using `only [Left.neg_neg_iff, Nat.cast_pos]`. Conclude with `this`. Rewrite using `[length_lpos, length_lneg]`. Conclude with `nP_add_nN_le _`. Rewrite using `[length_lpos, length_lneg]`.

Conclude with `nP_add_nN_le _`. Rewrite using `[length_lpos, length_lneg, nA, nD]`. Conclude with `nP_add_nN_le _`. Rewrite using `[length_lpos, length_lneg, nC, nB]`. Conclude with `nP_add_nN_le _`.

Use function extensionality and compare the values at `x`. Break down `x with i | j` into its components or cases. Conclude with `eq_pad (leftWeightFirst p q r s μ) iL1 s1 s2 i`. Conclude with `eq_pad (leftWeightSecond p q r s μ) firstRealIndex s3 s4 j`. Rewrite using `[eA, eB, eC, eD]`.

Use function extensionality and compare the values at `x`. Break down `x with k | l` into its components or cases. Conclude with `eq_pad (rightWeightFirst p q r s μ') iL2 s5 s6 k`. Conclude with `eq_pad (rightWeightSecond p q r s μ') secondRealIndex s7 s8 l`.
-/
theorem shape_from_facts : ShapeFromFacts := by
  intro p q r s μ μ' hB hS hI
  obtain ⟨hA, hBb, hC, hD⟩ := hB
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hS
  obtain ⟨hI1, hI2⟩ := hI
  have iL1 : ∀ i, ((⌊leftWeightFirst p q r s μ i⌋ : ℤ) : ℚ) = leftWeightFirst p q r s μ i := fun i => hI1 (.inl i)
  have firstRealIndex : ∀ j, ((⌊leftWeightSecond p q r s μ j⌋ : ℤ) : ℚ) = leftWeightSecond p q r s μ j := fun j => hI1 (.inr j)
  have iL2 : ∀ k, ((⌊rightWeightFirst p q r s μ' k⌋ : ℤ) : ℚ) = rightWeightFirst p q r s μ' k := fun k => hI2 (.inl k)
  have secondRealIndex : ∀ l, ((⌊rightWeightSecond p q r s μ' l⌋ : ℤ) : ℚ) = rightWeightSecond p q r s μ' l := fun l => hI2 (.inr l)
  have eA : lpos (αA p q r s μ) = lpos (αP (rightWeightFirst p q r s μ')) := lpos_eq_of_sq hA
  have eB : lneg (αB p q r s μ) = lneg (αN (rightWeightSecond p q r s μ')) := lneg_eq_of_sq hBb
  have eC : lpos (αC p q r s μ) = lpos (αP (rightWeightSecond p q r s μ')) := lpos_eq_of_sq hC
  have eD : lneg (αD p q r s μ) = lneg (αN (rightWeightFirst p q r s μ')) := lneg_eq_of_sq hD
  have nA : nP (leftWeightFirst p q r s μ) = nP (rightWeightFirst p q r s μ') := hA.1
  have nB : nN (leftWeightFirst p q r s μ) = nN (rightWeightSecond p q r s μ') := hBb.1
  have nC : nP (leftWeightSecond p q r s μ) = nP (rightWeightSecond p q r s μ') := hC.1
  have nD : nN (leftWeightSecond p q r s μ) = nN (rightWeightFirst p q r s μ') := hD.1
  refine ⟨lpos (αA p q r s μ), lneg (αB p q r s μ), lpos (αC p q r s μ), lneg (αD p q r s μ),
    ?_, ?_, ?_, ?_, pairwise_lpos hA.2.1, pairwise_lneg hBb.2.1, pairwise_lpos hC.2.1, pairwise_lneg hD.2.1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightFirst p q r s μ) iL1 s1 i
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightSecond p q r s μ) firstRealIndex s3 i
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightFirst p q r s μ) iL1 s2 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightSecond p q r s μ) firstRealIndex s4 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nA, nD]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nC, nB]; exact nP_add_nN_le _
  · funext x
    rcases x with i | j
    · exact eq_pad (leftWeightFirst p q r s μ) iL1 s1 s2 i
    · exact eq_pad (leftWeightSecond p q r s μ) firstRealIndex s3 s4 j
  · rw [eA, eB, eC, eD]
    funext x
    rcases x with k | l
    · exact eq_pad (rightWeightFirst p q r s μ') iL2 s5 s6 k
    · exact eq_pad (rightWeightSecond p q r s μ') secondRealIndex s7 s8 l

end PI.FJM
