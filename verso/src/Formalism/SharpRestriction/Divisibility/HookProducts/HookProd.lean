import Formalism.LocalToGlobal.Divisibility.Numbers

namespace Formalism.MainNotions.DIV.HookProducts

namespace HookLengthProduct

open Finset

def K (n : ℕ) (a : ℕ → ℕ) (c : ℕ) : ℕ := ((range n).filter (fun l => c < a l)).card

def E (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ c ∈ range (a i), ((a i - c) + (K n a c - i) - 1)

def D (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ l ∈ Ioo i n, (a i + l - a l - i)

def F (n : ℕ) (a : ℕ → ℕ) : ℕ := ∏ i ∈ range n, (a i + n - 1 - i).factorial

/- English proof (translation)
Simplify using `[K, Finset.range_add_one, Finset.filter_insert, h]`.
-/
theorem K_succ_of_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) (c : ℕ) : K (m + 1) a c = K m a c := by
  simp [K, Finset.range_add_one, Finset.filter_insert, h]

/- English proof (translation)
Unfold `K`. Rewrite using `[Finset.filter_true_of_mem, Finset.card_range]`. Introduce `l hl`. Use `h1 l (Finset.mem_range.mp hl)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem K_zero (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) : K n a 0 = n := by
  unfold K
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  omega

/- English proof (translation)
Unfold `K`. Use `congr 1`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `l hl`. Use `h1 l (Finset.mem_range.mp hl)` as an intermediate fact.

Use `show c + 1 < a l ↔ c < a l - 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem K_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) (c : ℕ) :
    K n a (c + 1) = K n (fun i => a i - 1) c := by
  unfold K
  congr 1
  apply Finset.filter_congr
  intro l hl
  have := h1 l (Finset.mem_range.mp hl)
  show c + 1 < a l ↔ c < a l - 1
  omega

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Rewrite using `[Finset.prod_range_succ', mul_comm, Nat.add_sub_cancel]`.
-/
theorem prod_range_pos (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℕ) :
    ∏ c ∈ range m, f c = f 0 * ∏ c ∈ range (m - 1), f (c + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_range_succ', mul_comm, Nat.add_sub_cancel]

/- English proof (translation)
Unfold `E`. Rewrite using `[Finset.prod_range_succ, h, Finset.range_zero, Finset.prod_empty, mul_one]`. Use `Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun c _ => ?_))` and prove the remaining obligations. Rewrite using `[K_succ_of_zero m a h c]`.
-/
theorem E_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) : E (m + 1) a = E m a := by
  unfold E
  rw [Finset.prod_range_succ, h, Finset.range_zero, Finset.prod_empty, mul_one]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun c _ => ?_))
  rw [K_succ_of_zero m a h c]

/- English proof (translation)
Unfold `D`. Rewrite using `[Finset.prod_range_succ]`. Establish `h0 : Ioo m (m + 1) = ∅`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `try omega`. Rewrite using `[h0, Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i < m` using `Finset.mem_range.mp hi`.

Establish `h1 : Ioo i (m + 1) = insert m (Ioo i m)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioo, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, Finset.prod_insert (by simp)]`.
-/
theorem D_succ (m : ℕ) (a : ℕ → ℕ) :
    D (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * D m a := by
  unfold D
  rw [Finset.prod_range_succ]
  have h0 : Ioo m (m + 1) = ∅ := by
    ext x
    simp only [Finset.mem_Ioo]
    simp
    try omega
  rw [h0, Finset.prod_empty, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have h1 : Ioo i (m + 1) = insert m (Ioo i m) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  rw [h1, Finset.prod_insert (by simp)]

/- English proof (translation)
Unfold `F`. Rewrite using `[Finset.prod_range_succ, ← Finset.prod_mul_distrib]`. Establish `hl : a m + (m + 1) - 1 - m = 0` using `by omega`. Rewrite using `[hl, Nat.factorial_zero, mul_one]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations.

Establish `hi' : i < m` using `Finset.mem_range.mp hi`. Establish `e1 : a i + (m + 1) - 1 - i = (a i + m - 1 - i) + 1` using `by omega`. Establish `e2 : a i + m - a m - i = (a i + m - 1 - i) + 1` using `by omega`. Rewrite using `[e1, e2, Nat.factorial_succ]`.
-/
theorem F_succ_zero (m : ℕ) (a : ℕ → ℕ) (h : a m = 0) :
    F (m + 1) a = (∏ i ∈ range m, (a i + m - a m - i)) * F m a := by
  unfold F
  rw [Finset.prod_range_succ, ← Finset.prod_mul_distrib]
  have hl : a m + (m + 1) - 1 - m = 0 := by omega
  rw [hl, Nat.factorial_zero, mul_one]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.mp hi
  have e1 : a i + (m + 1) - 1 - i = (a i + m - 1 - i) + 1 := by omega
  have e2 : a i + m - a m - i = (a i + m - 1 - i) + 1 := by omega
  rw [e1, e2, Nat.factorial_succ]

/- English proof (translation)
Simplify using `only [E]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i < n` using `Finset.mem_range.mp hi`. Establish `hai` using `h1 i hi'`.

Rewrite using `[prod_range_pos (a i) hai]`. Use `congr 1`. Rewrite using `[K_zero n a h1]`. Use linear arithmetic over natural numbers and integers. Use `Finset.prod_congr rfl (fun c _ => ?_)` and prove the remaining obligations.

Rewrite using `[K_shift n a h1 c]`. Use linear arithmetic over natural numbers and integers.
-/
theorem E_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    E n a = (∏ i ∈ range n, (a i + n - 1 - i)) * E n (fun i => a i - 1) := by
  simp only [E]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have hai := h1 i hi'
  rw [prod_range_pos (a i) hai]
  congr 1
  · rw [K_zero n a h1]
    omega
  · refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [K_shift n a h1 c]
    omega

/- English proof (translation)
Simplify using `only [D]`. Use `Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun l hl => ?_))` and prove the remaining obligations. Establish `hi' : i < n` using `Finset.mem_range.mp hi`. Establish `hl' : l < n` using `(Finset.mem_Ioo.mp hl).2`. Use `h1 i hi'` as an intermediate fact.

Use `h1 l hl'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem D_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    D n a = D n (fun i => a i - 1) := by
  simp only [D]
  refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun l hl => ?_))
  have hi' : i < n := Finset.mem_range.mp hi
  have hl' : l < n := (Finset.mem_Ioo.mp hl).2
  have := h1 i hi'
  have := h1 l hl'
  omega

/- English proof (translation)
Simplify using `only [F]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i < n` using `Finset.mem_range.mp hi`. Use `h1 i hi'` as an intermediate fact.

Establish `e : a i + n - 1 - i = (a i - 1 + n - 1 - i) + 1` using `by omega`. Rewrite using `[e, Nat.factorial_succ]`.
-/
theorem F_shift (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i) :
    F n a = (∏ i ∈ range n, (a i + n - 1 - i)) * F n (fun i => a i - 1) := by
  simp only [F]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have := h1 i hi'
  have e : a i + n - 1 - i = (a i - 1 + n - 1 - i) + 1 := by omega
  rw [e, Nat.factorial_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro a _`. Simplify using `[E, D, F]`. Consider the case `succ m ih`. It suffices to establish `H : ∀ k (a : ℕ → ℕ), a m = k → (∀ i l, i < l → l < m + 1 → a l ≤ a i) → E (m + 1) a * D (m + 1) a = F (m + 1) a from fun a h => H _ a rfl h`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a ha hmono`. Rewrite using `[E_succ_zero m a ha, D_succ, F_succ_zero m a ha, ← ih a (fun i l hil hl => hmono i l hil (by omega))]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `succ k ihk`. Introduce `a ha hmono`. Establish `h1 : ∀ i < m + 1, 1 ≤ a i`. Introduce `i hi`.

Break down `Nat.lt_or_ge i m with h | h` into its components or cases. Use `hmono i m h (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e : i = m` using `by omega`. Rewrite using `[e, ha]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[E_shift (m + 1) a h1, D_shift (m + 1) a h1, F_shift (m + 1) a h1, ← ihk (fun i => a i - 1) (by show a m - 1 = k; omega) (fun i l hil hl => by`. Use `hmono i l hil hl` as an intermediate fact. Use `show a l - 1 ≤ a i - 1`. Use the proof step `omega)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem E_mul_D (n : ℕ) :
    ∀ a : ℕ → ℕ, (∀ i l, i < l → l < n → a l ≤ a i) → E n a * D n a = F n a := by
  induction n with
  | zero => intro a _; simp [E, D, F]
  | succ m ih =>
    suffices H : ∀ k (a : ℕ → ℕ), a m = k → (∀ i l, i < l → l < m + 1 → a l ≤ a i) →
        E (m + 1) a * D (m + 1) a = F (m + 1) a from fun a h => H _ a rfl h
    intro k
    induction k with
    | zero =>
      intro a ha hmono
      rw [E_succ_zero m a ha, D_succ, F_succ_zero m a ha,
        ← ih a (fun i l hil hl => hmono i l hil (by omega))]
      ring
    | succ k ihk =>
      intro a ha hmono
      have h1 : ∀ i < m + 1, 1 ≤ a i := by
        intro i hi
        rcases Nat.lt_or_ge i m with h | h
        · have := hmono i m h (by omega)
          omega
        · have e : i = m := by omega
          rw [e, ha]
          omega
      rw [E_shift (m + 1) a h1, D_shift (m + 1) a h1, F_shift (m + 1) a h1,
        ← ihk (fun i => a i - 1) (by show a m - 1 = k; omega)
          (fun i l hil hl => by
            have := hmono i l hil hl
            show a l - 1 ≤ a i - 1
            omega)]
      ring

/- English proof (translation)
Substitute `hwe` using the available equality. Use `set μ := YoungDiagram.ofRowLens ((List.range n).map a) hw with hμ`. Establish `hmem : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i`. Introduce `i j`. Rewrite using `[hμ, YoungDiagram.mem_ofRowLens]`.

Simplify using the standard rewrite rules. Establish `hrow : ∀ i < n, μ.rowLen i = a i`. Introduce `i hi`. Apply `eq_of_forall_lt_iff` to reduce the goal to its premises. Introduce `j`.

Rewrite using `[← YoungDiagram.mem_iff_lt_rowLen, hmem]`. Simplify using `[hi]`. Establish `hcol : ∀ c, μ.colLen c = K n a c`. Introduce `c`. Establish `e : (range n).filter (fun l => c < a l) = range (μ.colLen c)`.

Use extensionality with `i`. Rewrite using `[Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen, hmem]`. Unfold `K`. Rewrite using `[e, Finset.card_range]`. Unfold `Formalism.LatticeIndexTer.hookProd E`.

Rewrite using `[Finset.prod_finset_product μ.cells (range n) (fun i => range (a i))]`. Use `Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun c _ => ?_))` and prove the remaining obligations. Rewrite using `[hrow i (Finset.mem_range.mp hi), hcol c]`. Introduce and unpack `⟨i, j⟩`. Rewrite using `[YoungDiagram.mem_cells, hmem]`.

Simplify using the standard rewrite rules.
-/
theorem hookProd_eq_E (n : ℕ) (a : ℕ → ℕ) (w : List ℕ) (hw : w.SortedGE)
    (hwe : w = (List.range n).map a) : Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens w hw) = E n a := by
  subst hwe
  set μ := YoungDiagram.ofRowLens ((List.range n).map a) hw with hμ
  have hmem : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i := by
    intro i j
    rw [hμ, YoungDiagram.mem_ofRowLens]
    simp
  have hrow : ∀ i < n, μ.rowLen i = a i := by
    intro i hi
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, hmem]
    simp [hi]
  have hcol : ∀ c, μ.colLen c = K n a c := by
    intro c
    have e : (range n).filter (fun l => c < a l) = range (μ.colLen c) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen,
        hmem]
    unfold K
    rw [e, Finset.card_range]
  unfold Formalism.LatticeIndexTer.hookProd E
  rw [Finset.prod_finset_product μ.cells (range n) (fun i => range (a i))]
  · refine Finset.prod_congr rfl (fun i hi => Finset.prod_congr rfl (fun c _ => ?_))
    rw [hrow i (Finset.mem_range.mp hi), hcol c]
  · rintro ⟨i, j⟩
    rw [YoungDiagram.mem_cells, hmem]
    simp

end HookLengthProduct

open HookLengthProduct in
/- English proof (translation)
Establish `hsorted : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a`. Apply `List.Pairwise.insertionSort_eq` to reduce the goal to its premises. Rewrite using `[List.pairwise_iff_getElem]`. Introduce `i j hi hj hij`. Simplify using `only [List.length_map, List.length_range] at hi hj`.

Simplify using `only [List.getElem_map, List.getElem_range]`. Conclude with `hmono i j hij hj`. Rewrite using `[hookProd_eq_E n a _ List.sortedGE_insertionSort hsorted]`. Conclude with `E_mul_D n a hmono`.
-/
theorem hookProd_mul_prod (n : ℕ) (a : ℕ → ℕ) (h1 : ∀ i < n, 1 ≤ a i)
    (hmono : ∀ i l, i < l → l < n → a l ≤ a i) :
    Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·))
              List.sortedGE_insertionSort) *
              (∏ i ∈ Finset.range n, ∏ l ∈ Finset.Ioo i n, (a i + l - a l - i)) =
      ∏ i ∈ Finset.range n, (a i + n - 1 - i).factorial := by
  have hsorted : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a := by
    apply List.Pairwise.insertionSort_eq
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.getElem_map, List.getElem_range]
    exact hmono i j hij hj
  rw [hookProd_eq_E n a _ List.sortedGE_insertionSort hsorted]
  exact E_mul_D n a hmono

end Formalism.MainNotions.DIV.HookProducts
