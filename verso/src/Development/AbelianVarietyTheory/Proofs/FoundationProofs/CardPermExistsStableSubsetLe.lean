import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FactorialLeTwoMulCardPermWithFixedPointStatement
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.StableSubset

open Finset Equiv

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Conclude with `Finset.mem_map' σ.toEmbedding`.
-/
theorem mem_iff_of_map_eq {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← h]
  exact Finset.mem_map' σ.toEmbedding

/- English proof (translation)
Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_map.1 hy`. Conclude with `h x hx`. Simplify using the standard rewrite rules.
-/
theorem map_eq_of_mem_iff {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact h x hx
  · simp

/- English proof (translation)
Establish `hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆ (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image (fun p => Perm.subtypeCongr p.1 p.2)`. Introduce `σ hσ`. Establish `h` using `mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2`. Use `Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Distinguish the cases in `hx : x ∈ A`. Simplify using `[Perm.subtypeCongr.left_apply _ _ hx]`. Simplify using `[Perm.subtypeCongr.right_apply _ _ hx]`. Use `(Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)` and prove the remaining obligations. Simplify using `[Fintype.card_perm, Fintype.card_subtype_compl]`.
-/
theorem card_stab_le {N : ℕ} (A : Finset (Fin N)) :
    (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆
      (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image
        (fun p => Perm.subtypeCongr p.1 p.2) := by
    intro σ hσ
    have h := mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2
    refine Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))),
      Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ A
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_perm, Fintype.card_subtype_compl]

/- English proof (translation)
Establish `c1 : Fintype.card {x // x ∈ A} = A.card` using `by simp`. Establish `c2 : Fintype.card {x // x ∉ A} = N - A.card` using `by simp [Fintype.card_subtype_compl]`. Establish `h1` using `GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∈ A} (Fintype.card_pos_iff.1 (by omega))`. Establish `h2` using `GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∉ A} (Fintype.card_pos_iff.1 (by omega))`. Rewrite `h1` using `[c1]`.

Rewrite `h2` using `[c2]`. Use `(Nat.mul_le_mul h1 h2).trans ?_` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, ← Finset.card_product]`. Use `Nat.mul_le_mul le_rfl ?_` and prove the remaining obligations. Use `Finset.card_le_card_of_injOn (fun p => Perm.subtypeCongr p.1 p.2) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `⟨e, f⟩ hp`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢`. Take `⟨⟨i, hi⟩, ⟨j, hj⟩⟩` from `hp`. Use `⟨map_eq_of_mem_iff _ _ ?_, ⟨i, i.2, ?_⟩, ⟨j, j.2, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[Perm.subtypeCongr.left_apply _ _ hx]`. Conclude with `(e ⟨x, hx⟩).2`. Rewrite using `[Perm.subtypeCongr.left_apply_subtype, hi]`. Rewrite using `[Perm.subtypeCongr.right_apply_subtype, hj]`. Introduce and unpack `⟨e, f⟩ - ⟨e', f'⟩ - h`.

Establish `h' : Perm.subtypeCongr e f = Perm.subtypeCongr e' f'` using `h`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `x : 2`. Use `congrArg (fun s : Perm (Fin N) => s x) h'` as an intermediate fact. Simplify `this` using `only [Perm.subtypeCongr.left_apply_subtype]`.

Use extensionality with `x : 2`. Use `congrArg (fun s : Perm (Fin N) => s x) h'` as an intermediate fact. Simplify `this` using `only [Perm.subtypeCongr.right_apply_subtype]`.
-/
theorem card_fix_ge {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card := by
  have c1 : Fintype.card {x // x ∈ A} = A.card := by simp
  have c2 : Fintype.card {x // x ∉ A} = N - A.card := by simp [Fintype.card_subtype_compl]
  have h1 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∈ A} (Fintype.card_pos_iff.1 (by omega))
  have h2 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∉ A} (Fintype.card_pos_iff.1 (by omega))
  rw [c1] at h1
  rw [c2] at h2
  refine (Nat.mul_le_mul h1 h2).trans ?_
  rw [mul_mul_mul_comm, ← Finset.card_product]
  refine Nat.mul_le_mul le_rfl ?_
  refine Finset.card_le_card_of_injOn (fun p => Perm.subtypeCongr p.1 p.2) ?_ ?_
  · rintro ⟨e, f⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hp
    refine ⟨map_eq_of_mem_iff _ _ ?_, ⟨i, i.2, ?_⟩, ⟨j, j.2, ?_⟩⟩
    · intro x hx
      rw [Perm.subtypeCongr.left_apply _ _ hx]
      exact (e ⟨x, hx⟩).2
    · rw [Perm.subtypeCongr.left_apply_subtype, hi]
    · rw [Perm.subtypeCongr.right_apply_subtype, hj]
  · rintro ⟨e, f⟩ - ⟨e', f'⟩ - h
    have h' : Perm.subtypeCongr e f = Perm.subtypeCongr e' f' := h
    refine Prod.ext ?_ ?_
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.left_apply_subtype] using this
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.right_apply_subtype] using this

noncomputable def wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N)) : ℕ :=
  if A.map σ.toEmbedding = A then
    (if (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j then 4 else 8) else 0

/- English proof (translation)
Establish `h1` using `card_stab_le A`. Establish `h2` using `card_fix_ge A h0 hN`. Establish `h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧ (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card = 8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card`. Rewrite using `[Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Unfold `wt`. Apply the tactic sequence `by_cases ha : A.map σ.toEmbedding = A <;>`. Apply the tactic sequence `by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_wt_le {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    ∑ σ, wt A σ ≤ 7 * (A.card.factorial * (N - A.card).factorial) := by
  have h1 := card_stab_le A
  have h2 := card_fix_ge A h0 hN
  have h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card =
      8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold wt
    by_cases ha : A.map σ.toEmbedding = A <;>
      by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp
  omega

/- English proof (translation)
Unfold `wt`. Rewrite using `[if_pos h]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem four_le_wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N))
    (h : A.map σ.toEmbedding = A) : 4 ≤ wt A σ := by
  unfold wt
  rw [if_pos h]
  split_ifs <;> omega

/- English proof (translation)
Establish `hAm : A ∈ powersetCard a (univ : Finset (Fin N))` using `by simp [hA]`. Distinguish the cases in `hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j`. Take `⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩` from `hb set B := insert j (A.erase i) with hB`. Establish `hjB : j ∈ B` using `Finset.mem_insert_self _ _`. Establish `hne : A ≠ B` using `fun e => hj (e ▸ hjB)`.

Establish `hBc : B.card = a`. Rewrite using `[hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)), Finset.card_erase_add_one hi, hA]`. Establish `hBm : B ∈ powersetCard a (univ : Finset (Fin N))` using `by simp [hBc]`. Establish `hBs : B.map σ.toEmbedding = B`. Apply `map_eq_of_mem_iff` to reduce the goal to its premises.

Introduce `x hx`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Rewrite using `[hσj]`. Conclude with `hjB`. Use `Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)` and prove the remaining obligations.

Introduce `e`. Conclude with `(Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))`. Conclude with `(mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2`. Establish `hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N))`. Introduce `C hC`.

Break down `Finset.mem_insert.1 hC with rfl | hC` into its components or cases. Conclude with `hAm`. Rewrite using `[Finset.mem_singleton.1 hC]`. Conclude with `hBm`. Use `Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs` as an intermediate fact.

Rewrite `this` using `[Finset.sum_pair hne]`. Establish `h1` using `four_le_wt A σ h`. Establish `h2` using `four_le_wt B σ hBs`. Use linear arithmetic over natural numbers and integers. Establish `: wt A σ = 8` using `by unfold wt; rw [if_pos h, if_neg hb]`.

Rewrite using `[← this]`. Conclude with `Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm`.
-/
theorem eight_le_sum_wt {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
  have hAm : A ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hA]
  by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j
  · obtain ⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩ := hb
    set B := insert j (A.erase i) with hB
    have hjB : j ∈ B := Finset.mem_insert_self _ _
    have hne : A ≠ B := fun e => hj (e ▸ hjB)
    have hBc : B.card = a := by
      rw [hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)),
        Finset.card_erase_add_one hi, hA]
    have hBm : B ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hBc]
    have hBs : B.map σ.toEmbedding = B := by
      apply map_eq_of_mem_iff
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [hσj]; exact hjB
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
        · intro e
          exact (Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))
        · exact (mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2
    have hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N)) := by
      intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hAm
      · rw [Finset.mem_singleton.1 hC]; exact hBm
    have := Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs
    rw [Finset.sum_pair hne] at this
    have h1 := four_le_wt A σ h
    have h2 := four_le_wt B σ hBs
    omega
  · have : wt A σ = 8 := by unfold wt; rw [if_pos h, if_neg hb]
    rw [← this]
    exact Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm

/- English proof (translation)
Introduce `N a h0 hN`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_filter, Finset.mul_sum]`. Use `Finset.sum_le_sum fun σ _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Take `⟨A, hA, h⟩` from `h`. Conclude with `eight_le_sum_wt σ A hA h`. Simplify using the standard rewrite rules. Use `_ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ := Finset.sum_comm`. Use `_ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), 7 * (a.factorial * (N - a).factorial) := by`.

Use `Finset.sum_le_sum fun B hB => ?_` and prove the remaining obligations. Establish `hB' : B.card = a` using `(Finset.mem_powersetCard.1 hB).2`. Use `sum_wt_le B (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[hB']`. Then use the resulting hypothesis. Use `_ = 7 * N.factorial := by`.

Rewrite using `[Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_exists_stable_subset_le : ∀ N a : ℕ, 0 < a → a < N →
    8 * (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A).card ≤ 7 * N.factorial := by
  intro N a h0 hN
  calc _ ≤ ∑ σ : Perm (Fin N), ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
        rw [Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with h
        · obtain ⟨A, hA, h⟩ := h
          exact eight_le_sum_wt σ A hA h
        · simp
    _ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ :=
        Finset.sum_comm
    _ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)),
          7 * (a.factorial * (N - a).factorial) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hB' : B.card = a := (Finset.mem_powersetCard.1 hB).2
        have := sum_wt_le B (by omega) (by omega)
        rwa [hB'] at this
    _ = 7 * N.factorial := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]
        ring

end GlobalTheory.StableSubset
