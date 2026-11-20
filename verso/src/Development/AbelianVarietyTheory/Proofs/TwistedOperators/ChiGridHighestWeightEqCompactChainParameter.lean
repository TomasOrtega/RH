import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.ChiGrid GlobalTheory.RowReal
open Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.RowReal.WeightsX

open GlobalTheory.SignedHC

/- English proof (translation)
Rewrite using `[GlobalTheory.SignedHC.mem_block]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]`. Conclude with `⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩`.
-/
theorem mem_listBlock_iff {c x : ℚ} {n : ℕ} : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n ↔ x ∈ TPar.block c n := by
  rw [GlobalTheory.SignedHC.mem_block]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block`. Rewrite using `[List.pairwise_map]`. Use `(List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_` and prove the remaining obligations. Establish `: (a : ℚ) < b` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pairwise_listBlock (c : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  linarith

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiPar_eq (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar =
    (num D C τ).a 0 :: ((List.finRange D.R.m).flatMap (fun i : Fin D.R.m =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)]) ++
      (List.finRange (D.R.k - 1)).map fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)) := rfl

/- English proof (translation)
Establish `hm : (num D C τ).NearMid` using `num_nearMid D C τ`. Establish `hs : 1 ≤ (num D C τ).s` using `(odd_sLen D).pos`. Establish `hg : (num D C τ).s < (num D C τ).ga` using `sLen_lt_gap D C`. Establish `hGm : (num D C τ).m = D.R.m` using `rfl`. Establish `hGk : (num D C τ).k = D.R.k` using `rfl`.

Establish `hga : (0 : ℚ) < (num D C τ).ga` using `by exact_mod_cast (by omega : 0 < (num D C τ).ga)`. Establish `hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i` using `fun h => by`. Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Combine the linear relations using `[a_add_le (G := num D C τ) h]`.

Establish `hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) → (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga` using `fun i x hx => blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)`. Establish `piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i`. Introduce `i y hy`. Rewrite using `[(num D C τ).a_eq_succ_add i]`. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Use `hB i y h` as an intermediate fact. Conclude with `⟨this.1.le, this.2⟩`. Rewrite `h` using `[List.mem_singleton]`. Substitute `h` using the available equality. Conclude with `⟨le_rfl, by linarith⟩`.

Establish `hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)), y ∈ (num D C τ).cloudHalf`. Introduce `y hy`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩`. Rewrite using `[psiPar_eq]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]`. Use `⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `y hy`. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Take `⟨i, -, h⟩` from `List.mem_flatMap.1 h`. Use `piece i y h` as an intermediate fact. Combine the linear relations using `[hle (Nat.zero_le (i : ℕ))]`. Use `cloudHalf_lt (hU y h)` as an intermediate fact. Combine the linear relations using `[hle (Nat.zero_le (num D C τ).m)]`.

Introduce `i _`. Rewrite using `[List.pairwise_append]`. Use `⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Rewrite `hy` using `[List.mem_singleton]`.

Substitute `hy` using the available equality. Conclude with `(hB i x hx).1`. Use `(List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_` and prove the remaining obligations. Introduce `x hx y hy`. Establish `h1` using `piece i x hx`.

Establish `h2` using `piece j y hy`. Establish `h3 : (i : ℕ) + 1 ≤ j` using `hij`. Combine the linear relations using `[hle h3]`. Use `(List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_` and prove the remaining obligations. Establish `hij' : (i : ℕ) < j` using `hij`.

Use `(num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)` as an intermediate fact. Establish `h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2)` using `by exact_mod_cast this`. Simplify using `only [GridData.vHalf]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx y hy`.

Take `⟨i, -, h⟩` from `List.mem_flatMap.1 hx`. Establish `h1` using `piece i x h`. Establish `h2` using `cloudHalf_lt (hU y hy)`. Establish `h3 : (i : ℕ) + 1 ≤ (num D C τ).m` using `by have := i.2; omega`. Combine the linear relations using `[hle h3]`.

Introduce `y hy`. Rewrite using `[GridData.mem_weightX]`. Break down `List.mem_cons.1 hy with rfl | hy` into its components or cases. Conclude with `Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)`. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Take `⟨i, -, h⟩` from `List.mem_flatMap.1 h`. Break down `List.mem_append.1 h with h | h` into its components or cases. Conclude with `Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))`. Rewrite `h` using `[List.mem_singleton]`. Substitute `h` using the available equality.

Conclude with `Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)`. Conclude with `Or.inr (Or.inl (hU y h))`.
-/
theorem psiPar_props (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    (rowEntries D C τ).psiPar.Pairwise (· > ·) ∧ ∀ x ∈ (rowEntries D C τ).psiPar, x ∈ (num D C τ).weightX 0 := by
  have hm : (num D C τ).NearMid := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  have hGm : (num D C τ).m = D.R.m := rfl
  have hGk : (num D C τ).k = D.R.k := rfl
  have hga : (0 : ℚ) < (num D C τ).ga := by exact_mod_cast (by omega : 0 < (num D C τ).ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) →
      (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga := fun i x hx =>
    blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)
  have piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++
      [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i := by
    intro i y hy
    rw [(num D C τ).a_eq_succ_add i]
    rcases List.mem_append.1 hy with h | h
    · have := hB i y h; exact ⟨this.1.le, this.2⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨le_rfl, by linarith⟩
  have hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)),
      y ∈ (num D C τ).cloudHalf := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩
  rw [psiPar_eq]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
        have := piece i y h
        linarith [hle (Nat.zero_le (i : ℕ))]
      · have := cloudHalf_lt (hU y h)
        linarith [hle (Nat.zero_le (num D C τ).m)]
    · intro i _
      rw [List.pairwise_append]
      refine ⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hB i x hx).1
    · refine (List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_
      intro x hx y hy
      have h1 := piece i x hx
      have h2 := piece j y hy
      have h3 : (i : ℕ) + 1 ≤ j := hij
      linarith [hle h3]
    · refine (List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_
      have hij' : (i : ℕ) < j := hij
      have := (num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)
      have h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2) := by exact_mod_cast this
      simp only [GridData.vHalf]; linarith
    · intro x hx y hy
      obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hx
      have h1 := piece i x h
      have h2 := cloudHalf_lt (hU y hy)
      have h3 : (i : ℕ) + 1 ≤ (num D C τ).m := by have := i.2; omega
      linarith [hle h3]
  · intro y hy
    rw [GridData.mem_weightX]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))
      · rw [List.mem_singleton] at h; subst h
        exact Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)
    · exact Or.inr (Or.inl (hU y h))

/- English proof (translation)
Rewrite using `[length_psi, rowSizes_nR]`. Simplify using `[rankX]`.
-/
theorem length_psiPar (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar.length = rankP D D.R.m := by
  rw [length_psi, rowSizes_nR]; simp [rankX]

end GlobalTheory.RowReal.WeightsX

namespace GlobalTheory.RowReal

open GlobalTheory.SignedHC GlobalTheory.RowReal.WeightsX

end GlobalTheory.RowReal
