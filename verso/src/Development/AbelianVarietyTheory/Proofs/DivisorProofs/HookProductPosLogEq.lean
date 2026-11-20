import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HookREqHookProd

namespace GlobalTheory.HookDiagram

/- English proof (translation)
Establish `hrow : ∀ r, r < n → μ.rowLen r = a r`. Introduce `r hr`. Apply `le_antisymm` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Establish `hm : (r, a r) ∈ μ` using `YoungDiagram.mem_iff_lt_rowLen.mpr hlt`. Conclude with `lt_irrefl _ ((h r (a r)).mp hm).2`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hm : (r, μ.rowLen r) ∈ μ` using `(h r _).mpr ⟨hr, hlt⟩`.

Conclude with `lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)`. Establish `hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) = Finset.Ioo r (μ.colLen c)`. Introduce `r c`. Use extensionality with `r'`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioo]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Conclude with `⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `hm` using `(h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)`.

Conclude with `⟨⟨h1, hm.1⟩, hm.2⟩`. Establish `hrc : ∀ r c, r < n → c < a r → r < μ.colLen c` using `fun r c hr hc => YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)`. Unfold `Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd`. Rewrite using `[Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `r hr`. Rewrite `hr` using `[Finset.mem_range]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_range]`.

Simplify using `only`. Rewrite using `[hcol r c, Nat.card_Ioo, hrow r hr]`. Use `hrc r c hr hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨i, j⟩`.

Simplify using `only [YoungDiagram.mem_cells, Finset.mem_range]`. Conclude with `h i j`.
-/
theorem hookProd_eq_of_mem (μ : YoungDiagram) (n : ℕ) (a : ℕ → ℕ)
    (h : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i) :
    Formalism.LatticeIndexTer.hookProd μ = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hrow : ∀ r, r < n → μ.rowLen r = a r := by
    intro r hr
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, a r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      exact lt_irrefl _ ((h r (a r)).mp hm).2
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, μ.rowLen r) ∈ μ := (h r _).mpr ⟨hr, hlt⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
  have hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) =
      Finset.Ioo r (μ.colLen c) := by
    intro r c
    ext r'
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩
    · rintro ⟨h1, h2⟩
      have hm := (h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)
      exact ⟨⟨h1, hm.1⟩, hm.2⟩
  have hrc : ∀ r c, r < n → c < a r → r < μ.colLen c := fun r c hr hc =>
    YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)
  unfold Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd
  rw [Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]
  · apply Finset.prod_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    dsimp only
    rw [hcol r c, Nat.card_Ioo, hrow r hr]
    have := hrc r c hr hc
    omega
  · rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    exact h i j

/- English proof (translation)
Establish `hsort : ((List.range n).map a).Pairwise (· ≥ ·)`. Rewrite using `[List.pairwise_map]`. Conclude with `List.pairwise_lt_range.imp_of_mem (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))`. Establish `hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a` using `hsort.insertionSort_eq`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf`.

Apply `hookProd_eq_of_mem` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[YoungDiagram.mem_ofRowLens]`. Simplify using `only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range, exists_prop]`.
-/
theorem hookOf_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hsort : ((List.range n).map a).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem
      (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))
  have hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a :=
    hsort.insertionSort_eq
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf
  apply hookProd_eq_of_mem
  intro i j
  rw [YoungDiagram.mem_ofRowLens]
  simp only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
    exists_prop]

/- English proof (translation)
Rewrite using `[hookOf_eq n a ha]`. Establish `hm` using `GlobalTheory.LiftSizeCompare.hookProd_mul n a ha`. Establish `hinner : ∀ r ∈ Finset.range n, 0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r))`. Introduce `r _`. Apply `Finset.prod_pos` to reduce the goal to its premises.

Introduce `l hl`. Rewrite `hl` using `[Finset.mem_Ioo]`. Use linear arithmetic over natural numbers and integers. Establish `hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r))` using `Finset.prod_pos hinner`. Establish `hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a`.

Break down `Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0` into its components or cases. Establish `hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial` using `Finset.prod_pos fun r _ => Nat.factorial_pos _`. Rewrite `hm` using `[h0, zero_mul]`. Use linear arithmetic over natural numbers and integers. Conclude with `h0`.

Use `⟨hHpos, ?_⟩` and prove the remaining obligations. Establish `hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) = ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) / ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ)`. Rewrite using `[eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]`. Establish `hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ)`. Conclude with `Finset.prod_pos fun r _ => Nat.factorial_pos _` after adjusting the coercions.

Rewrite using `[hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]`. Unfold `Formalism.BasicNotions.DV.logHook`. Use `congr 1`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `r hr`. Rewrite `hr` using `[Finset.mem_range]`. Establish `hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1`. Rewrite using `[Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg, Real.Gamma_nat_eq_factorial]`. Introduce `r _`. Conclude with `(Nat.factorial_pos _).ne'` after adjusting the coercions. Rewrite using `[Nat.cast_prod, Real.log_prod]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `r hr`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l hl`.

Rewrite `hl` using `[Finset.mem_Ioo]`. Establish `hal : a l ≤ a r` using `ha r l hl.1.le hl.2`. Use `congr 1`. Rewrite using `[Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `l hl`. Rewrite `hl` using `[Finset.mem_Ioo]`. Establish `hpos : 0 < a r - a l + (l - r)` using `by omega`. Conclude with `hpos.ne'` after adjusting the coercions. Introduce `r hr`.

Conclude with `(hinner r hr).ne'` after adjusting the coercions.
-/
theorem hookOf_pos_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a ∧
      Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) = Formalism.BasicNotions.DV.logHook n (fun k => (a k : ℝ)) := by
  rw [hookOf_eq n a ha]
  have hm := GlobalTheory.LiftSizeCompare.hookProd_mul n a ha
  have hinner : ∀ r ∈ Finset.range n,
      0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) := by
    intro r _
    apply Finset.prod_pos
    intro l hl
    rw [Finset.mem_Ioo] at hl
    omega
  have hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) :=
    Finset.prod_pos hinner
  have hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
    rcases Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0
    · have hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial :=
        Finset.prod_pos fun r _ => Nat.factorial_pos _
      rw [h0, zero_mul] at hm
      omega
    · exact h0
  refine ⟨hHpos, ?_⟩
  have hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) =
      ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) /
        ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]
  have hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun r _ => Nat.factorial_pos _
  rw [hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]
        push_cast
        ring
      rw [hg, Real.Gamma_nat_eq_factorial]
    · intro r _
      exact_mod_cast (Nat.factorial_pos _).ne'
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mem_Ioo] at hl
        have hal : a l ≤ a r := ha r l hl.1.le hl.2
        congr 1
        rw [Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]
        ring
      · intro l hl
        rw [Finset.mem_Ioo] at hl
        have hpos : 0 < a r - a l + (l - r) := by omega
        exact_mod_cast hpos.ne'
    · intro r hr
      exact_mod_cast (hinner r hr).ne'

end GlobalTheory.HookDiagram
