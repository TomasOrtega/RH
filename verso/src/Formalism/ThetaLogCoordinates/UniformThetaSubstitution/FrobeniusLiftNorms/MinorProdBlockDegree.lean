import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

/- English proof (translation)
Distinguish the cases in `hA : ∃ k ∈ S, 2 ≤ β k`. Conclude with `Or.inl hA`. Use `right`. Assume the negation of the conclusion as `hB`. Establish `hle : ∀ k ∈ S, β k ≤ 1` using `fun k hk => by`.

Assume the negation of the conclusion as `h'`. Conclude with `hA ⟨k, hk, by omega⟩`. Establish `hcard : (S.filter (fun k => β k ≠ 0)).card ≤ 1`. Rewrite using `[Finset.card_le_one]`. Introduce `a ha b hb`.

Rewrite `ha`, `hb` using `[Finset.mem_filter]`. Assume the negation of the conclusion as `hab`. Conclude with `hB ⟨a, ha.1, b, hb.1, hab, Nat.one_le_iff_ne_zero.mpr ha.2, Nat.one_le_iff_ne_zero.mpr hb.2⟩`. Establish `hsum : ∑ k ∈ S, β k ≤ (S.filter (fun k => β k ≠ 0)).card`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_filter_ne_zero]`. Use `_ ≤ ∑ k ∈ S.filter (fun k => β k ≠ 0), 1 := Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)`. Use `_ = (S.filter (fun k => β k ≠ 0)).card := by simp`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_two_le_or_two_pos_of_one_lt_sum {κ : Type} (S : Finset κ) (β : κ →₀ ℕ)
    (h : 1 < ∑ k ∈ S, β k) :
    (∃ k ∈ S, 2 ≤ β k) ∨ ∃ k ∈ S, ∃ k' ∈ S, k ≠ k' ∧ 1 ≤ β k ∧ 1 ≤ β k' := by
  by_cases hA : ∃ k ∈ S, 2 ≤ β k
  · exact Or.inl hA
  right
  by_contra hB
  have hle : ∀ k ∈ S, β k ≤ 1 := fun k hk => by
    by_contra h'
    exact hA ⟨k, hk, by omega⟩
  have hcard : (S.filter (fun k => β k ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact hB ⟨a, ha.1, b, hb.1, hab, Nat.one_le_iff_ne_zero.mpr ha.2,
      Nat.one_le_iff_ne_zero.mpr hb.2⟩
  have hsum : ∑ k ∈ S, β k ≤ (S.filter (fun k => β k ≠ 0)).card := by
    calc ∑ k ∈ S, β k = ∑ k ∈ S.filter (fun k => β k ≠ 0), β k := by
          rw [Finset.sum_filter_ne_zero]
      _ ≤ ∑ k ∈ S.filter (fun k => β k ≠ 0), 1 :=
          Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)
      _ = (S.filter (fun k => β k ≠ 0)).card := by simp
  omega

/- English proof (translation)
Introduce `K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ hpos hξ β hβ`. Use `h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s₀ then 1 else 0) S ?hf β ?hsum` and prove the remaining obligations. Use `case hf =>`. Introduce `c β' hc`. Apply the tactic sequence `try dsimp only at hc`.

Apply `h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'` to reduce the goal to its premises. Distinguish the cases in `hs : sf c = s₀`. Rewrite `hc` using `[if_pos hs]`. Break down `exists_two_le_or_two_pos_of_one_lt_sum S β' hc with ⟨k, _, h2k⟩ | ⟨k, hk, k', hk', hne, h1k, h1k'⟩` into its components or cases. Conclude with `Or.inl ⟨k, h2k⟩`.

Conclude with `Or.inr (Or.inl ⟨k, k', hne, h1k, h1k', (hpos k hk).trans (hpos k' hk').symm, Or.inl (hξ k hk k' hk')⟩)`. Rewrite `hc` using `[if_neg hs]`. Take `⟨k, hk, hk0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hc.ne'`. Conclude with `Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)`. Use `case hsum =>`.

Rewrite `hβ` using `[Finset.card_filter]`. Conclude with `hβ`.
-/
theorem HitsCapPos_of (h1 : HasseDerivProdVanish) (h2 : MinorHits) : HitsCapPos := by
  intro K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ hpos hξ β hβ
  refine h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C
    (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s₀ then 1 else 0) S ?hf β ?hsum
  case hf =>
    intro c β' hc
    try dsimp only at hc
    apply h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'
    by_cases hs : sf c = s₀
    · rw [if_pos hs] at hc
      rcases exists_two_le_or_two_pos_of_one_lt_sum S β' hc with ⟨k, _, h2k⟩ | ⟨k, hk, k', hk', hne, h1k, h1k'⟩
      · exact Or.inl ⟨k, h2k⟩
      · exact Or.inr (Or.inl ⟨k, k', hne, h1k, h1k', (hpos k hk).trans (hpos k' hk').symm,
          Or.inl (hξ k hk k' hk')⟩)
    · rw [if_neg hs] at hc
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc.ne'
      exact Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0,
        Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)
  case hsum =>
    rw [Finset.card_filter] at hβ
    exact hβ

/- English proof (translation)
Introduce `K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ J hpos hJ β hβ`. Use `h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s₀ then ((univ.image (I c)) ∩ J).card else 0) S ?hf β ?hsum` and prove the remaining obligations. Use `case hf =>`. Introduce `c β' hc`. Apply the tactic sequence `try dsimp only at hc`.

Apply `h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'` to reduce the goal to its premises. Distinguish the cases in `hs : sf c = s₀`. Rewrite `hc` using `[if_pos hs]`. Assume the negation of the conclusion as `hno`. Apply `absurd hc` to reduce the goal to its premises.

Rewrite using `[not_lt]`. Establish `hle : ∀ k ∈ S, β' k ≤ 1` using `fun k _ => by`. Assume the negation of the conclusion as `h'`. Conclude with `hno (Or.inl ⟨k, by omega⟩)`. Establish `hinj : ∀ k ∈ S.filter (fun k => β' k ≠ 0), ∀ k' ∈ S.filter (fun k => β' k ≠ 0), col k = col k' → k = k'`.

Introduce `k hk k' hk' hcol`. Rewrite `hk`, `hk'` using `[Finset.mem_filter]`. Assume the negation of the conclusion as `hne`. Conclude with `hno (Or.inr (Or.inl ⟨k, k', hne, Nat.one_le_iff_ne_zero.mpr hk.2, Nat.one_le_iff_ne_zero.mpr hk'.2, (hpos k hk.1).trans (hpos k' hk'.1).symm, Or.inr hcol⟩))`. Establish `hmaps : ∀ k ∈ S.filter (fun k => β' k ≠ 0), col k ∈ (univ.image (I c)) ∩ J`.

Introduce `k hk`. Rewrite `hk` using `[Finset.mem_filter]`. Rewrite using `[Finset.mem_inter]`. Use `⟨?_, hJ k hk.1⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`.

Conclude with `hno (Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk.2, Or.inr (fun hr => by`. Take `⟨i, hi⟩` from `Set.mem_range.mp hr`. Conclude with `hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))⟩))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_filter_ne_zero]`.

Use `_ ≤ ∑ k ∈ S.filter (fun k => β' k ≠ 0), 1 := Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)`. Use `_ = (S.filter (fun k => β' k ≠ 0)).card := by simp`. Use `_ ≤ ((univ.image (I c)) ∩ J).card := Finset.card_le_card_of_injOn col (fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk))) (fun k hk k' hk' h => hinj k (Finset.mem_coe.mp hk) k' (Finset.mem_coe.mp hk') h)`. Rewrite `hc` using `[if_neg hs]`. Take `⟨k, hk, hk0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hc.ne'`.

Conclude with `Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)`. Use `case hsum =>`. Rewrite `hβ` using `[Finset.sum_filter]`. Conclude with `hβ`.
-/
theorem HitsColumnsPos_of (h1 : HasseDerivProdVanish) (h2 : MinorHits) : HitsColumnsPos := by
  intro K σ κ _ _ _ r0 r1 C l sf T I pos ξ col S s₀ J hpos hJ β hβ
  refine h1 K (σ × Fin r0 × Fin r1) κ (fun k => colDir (pos k) (ξ k) (col k)) C
    (fun c => minorAt (sf c) (T c) (I c))
    (fun c => if sf c = s₀ then ((univ.image (I c)) ∩ J).card else 0) S ?hf β ?hsum
  case hf =>
    intro c β' hc
    try dsimp only at hc
    apply h2 K σ κ r0 r1 (l c) (sf c) (T c) (I c) pos ξ col β'
    by_cases hs : sf c = s₀
    · rw [if_pos hs] at hc
      by_contra hno
      apply absurd hc
      rw [not_lt]
      have hle : ∀ k ∈ S, β' k ≤ 1 := fun k _ => by
        by_contra h'
        exact hno (Or.inl ⟨k, by omega⟩)
      have hinj : ∀ k ∈ S.filter (fun k => β' k ≠ 0), ∀ k' ∈ S.filter (fun k => β' k ≠ 0),
          col k = col k' → k = k' := by
        intro k hk k' hk' hcol
        rw [Finset.mem_filter] at hk hk'
        by_contra hne
        exact hno (Or.inr (Or.inl ⟨k, k', hne, Nat.one_le_iff_ne_zero.mpr hk.2,
          Nat.one_le_iff_ne_zero.mpr hk'.2, (hpos k hk.1).trans (hpos k' hk'.1).symm, Or.inr hcol⟩))
      have hmaps : ∀ k ∈ S.filter (fun k => β' k ≠ 0), col k ∈ (univ.image (I c)) ∩ J := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_inter]
        refine ⟨?_, hJ k hk.1⟩
        by_contra hnot
        exact hno (Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk.2, Or.inr (fun hr => by
          obtain ⟨i, hi⟩ := Set.mem_range.mp hr
          exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))⟩))
      calc ∑ k ∈ S, β' k = ∑ k ∈ S.filter (fun k => β' k ≠ 0), β' k := by
            rw [Finset.sum_filter_ne_zero]
        _ ≤ ∑ k ∈ S.filter (fun k => β' k ≠ 0), 1 :=
            Finset.sum_le_sum (fun k hk => hle k (Finset.mem_filter.mp hk).1)
        _ = (S.filter (fun k => β' k ≠ 0)).card := by simp
        _ ≤ ((univ.image (I c)) ∩ J).card :=
            Finset.card_le_card_of_injOn col
              (fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk)))
              (fun k hk k' hk' h => hinj k (Finset.mem_coe.mp hk) k' (Finset.mem_coe.mp hk') h)
    · rw [if_neg hs] at hc
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc.ne'
      exact Or.inr (Or.inr ⟨k, Nat.one_le_iff_ne_zero.mpr hk0,
        Or.inl (fun h => hs (h.symm.trans (hpos k hk)))⟩)
  case hsum =>
    rw [Finset.sum_filter] at hβ
    exact hβ

section BiLe

variable {K ι κ : Type} [Field K]

def BiLe (n0 : ι →₀ ℕ) (W : MvPolynomial κ (MvPolynomial ι K)) : Prop :=
  ∀ β : κ →₀ ℕ, ∀ n ∈ (MvPolynomial.coeff β W).support, n ≤ n0 ∧ n.degree + β.degree = n0.degree

/- English proof (translation)
Introduce `β n hn`. Simplify using `at hn`.
-/
lemma biLe_zero (n0 : ι →₀ ℕ) : BiLe n0 (0 : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  simp at hn

/- English proof (translation)
Introduce `β n hn`. Rewrite `hn` using `[MvPolynomial.coeff_add]`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hn) with hn1 | hn1` into its components or cases. Conclude with `h β n hn1`. Conclude with `h' β n hn1`.
-/
lemma biLe_add {n0 : ι →₀ ℕ} {W W' : MvPolynomial κ (MvPolynomial ι K)} (h : BiLe n0 W)
    (h' : BiLe n0 W') : BiLe n0 (W + W') := by
  classical
  intro β n hn
  rw [MvPolynomial.coeff_add] at hn
  rcases Finset.mem_union.mp (MvPolynomial.support_add hn) with hn1 | hn1
  · exact h β n hn1
  · exact h' β n hn1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `biLe_zero n0`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `biLe_add (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))`.
-/
lemma biLe_sum {α : Type*} {n0 : ι →₀ ℕ} (s : Finset α)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe n0 (W a)) :
    BiLe n0 (∑ a ∈ s, W a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact biLe_zero n0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact biLe_add (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/- English proof (translation)
Introduce `β n hn`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul, MvPolynomial.coeff_sum]`. Take `⟨q, hq, hq0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hn`. Rewrite `hq0` using `[MvPolynomial.coeff_mul]`. Take `⟨r, hr, hr0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hq0`.

Rewrite `hq`, `hr` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hA : r.1 ∈ (MvPolynomial.coeff q.1 W).support` using `MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hr0)`. Establish `hB : r.2 ∈ (MvPolynomial.coeff q.2 W').support` using `MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hr0)`. Take `⟨hA1, hA2⟩` from `h q.1 r.1 hA`. Take `⟨hB1, hB2⟩` from `h' q.2 r.2 hB`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr]`. Conclude with `add_le_add hA1 hB1`. Rewrite using `[← hr, ← hq]`. Simplify using `only [map_add]`.

Use linear arithmetic over natural numbers and integers.
-/
lemma biLe_mul {n0 n0' : ι →₀ ℕ} {W W' : MvPolynomial κ (MvPolynomial ι K)} (h : BiLe n0 W)
    (h' : BiLe n0' W') : BiLe (n0 + n0') (W * W') := by
  classical
  intro β n hn
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul, MvPolynomial.coeff_sum] at hn
  obtain ⟨q, hq, hq0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [MvPolynomial.coeff_mul] at hq0
  obtain ⟨r, hr, hr0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq0
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq hr
  have hA : r.1 ∈ (MvPolynomial.coeff q.1 W).support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hr0)
  have hB : r.2 ∈ (MvPolynomial.coeff q.2 W').support :=
    MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hr0)
  obtain ⟨hA1, hA2⟩ := h q.1 r.1 hA
  obtain ⟨hB1, hB2⟩ := h' q.2 r.2 hB
  refine ⟨?_, ?_⟩
  · rw [← hr]
    exact add_le_add hA1 hB1
  · rw [← hr, ← hq]
    simp only [map_add]
    omega

/- English proof (translation)
Rewrite `hn` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one]`. Assume the negation of the conclusion as `h`. Conclude with `hn (if_neg (Ne.symm h))`.
-/
private theorem eq_zero_of_mem_support_one {R σ : Type*} [CommSemiring R] {n : σ →₀ ℕ}
    (hn : n ∈ (1 : MvPolynomial σ R).support) : n = 0 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hn
  by_contra h
  exact hn (if_neg (Ne.symm h))

/- English proof (translation)
Rewrite `hn` using `[MvPolynomial.coeff_C]`. Distinguish the cases in `hβ : (0 : κ' →₀ ℕ) = β`. Rewrite `hn` using `[if_pos hβ]`. Conclude with `⟨hβ.symm, hn⟩`. Rewrite `hn` using `[if_neg hβ]`.

Simplify using `at hn`.
-/
private theorem eq_zero_and_mem_support_of_mem_support_coeff_C {R σ κ' : Type*} [CommSemiring R] {P : MvPolynomial σ R}
    {β : κ' →₀ ℕ} {n : σ →₀ ℕ}
    (hn : n ∈ (MvPolynomial.coeff β (MvPolynomial.C P : MvPolynomial κ' (MvPolynomial σ R))).support) :
    β = 0 ∧ n ∈ P.support := by
  classical
  rw [MvPolynomial.coeff_C] at hn
  by_cases hβ : (0 : κ' →₀ ℕ) = β
  · rw [if_pos hβ] at hn
    exact ⟨hβ.symm, hn⟩
  · rw [if_neg hβ] at hn
    simp at hn

/- English proof (translation)
Introduce `β n hn`. Take `⟨hβ, hn'⟩` from `eq_zero_and_mem_support_of_mem_support_coeff_C (P := (1 : MvPolynomial ι K)) (β := β) (n := n) (by rw [MvPolynomial.C_1]; exact hn)`. Take `rfl` from `eq_zero_of_mem_support_one hn'`. Substitute `hβ` using the available equality. Conclude with `⟨le_rfl, by simp⟩`.
-/
lemma biLe_one : BiLe 0 (1 : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  obtain ⟨hβ, hn'⟩ := eq_zero_and_mem_support_of_mem_support_coeff_C (P := (1 : MvPolynomial ι K)) (β := β) (n := n)
    (by rw [MvPolynomial.C_1]; exact hn)
  obtain rfl := eq_zero_of_mem_support_one hn'
  subst hβ
  exact ⟨le_rfl, by simp⟩

/- English proof (translation)
Rewrite `hn` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]`. Assume the negation of the conclusion as `h`. Conclude with `hn (if_neg (Ne.symm h))`.
-/
private theorem eq_zero_of_mem_support_C {R σ : Type*} [CommSemiring R] {a : R} {n : σ →₀ ℕ}
    (hn : n ∈ (MvPolynomial.C a : MvPolynomial σ R).support) : n = 0 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hn
  by_contra h
  exact hn (if_neg (Ne.symm h))

/- English proof (translation)
Introduce `β n hn`. Take `⟨hβ, hn'⟩` from `eq_zero_and_mem_support_of_mem_support_coeff_C hn`. Take `rfl` from `eq_zero_of_mem_support_C hn'`. Substitute `hβ` using the available equality. Conclude with `⟨le_rfl, by simp⟩`.
-/
lemma biLe_CC (a : K) :
    BiLe 0 (MvPolynomial.C (MvPolynomial.C a) : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  obtain ⟨hβ, hn'⟩ := eq_zero_and_mem_support_of_mem_support_coeff_C hn
  obtain rfl := eq_zero_of_mem_support_C hn'
  subst hβ
  exact ⟨le_rfl, by simp⟩

/- English proof (translation)
Rewrite `hn` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_X]`. Assume the negation of the conclusion as `h`. Conclude with `hn (if_neg (Ne.symm h))`.
-/
private theorem eq_single_of_mem_support_X {R σ : Type*} [CommSemiring R] {x : σ} {n : σ →₀ ℕ}
    (hn : n ∈ (MvPolynomial.X x : MvPolynomial σ R).support) : n = Finsupp.single x 1 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at hn
  by_contra h
  exact hn (if_neg (Ne.symm h))

/- English proof (translation)
Introduce `β n hn`. Take `⟨hβ, hn'⟩` from `eq_zero_and_mem_support_of_mem_support_coeff_C hn`. Take `rfl` from `eq_single_of_mem_support_X hn'`. Substitute `hβ` using the available equality. Conclude with `⟨le_rfl, by simp⟩`.
-/
lemma biLe_CX (x : ι) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.X x) : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  obtain ⟨hβ, hn'⟩ := eq_zero_and_mem_support_of_mem_support_coeff_C hn
  obtain rfl := eq_single_of_mem_support_X hn'
  subst hβ
  exact ⟨le_rfl, by simp⟩

/- English proof (translation)
Introduce `β n hn`. Rewrite `hn` using `[MvPolynomial.coeff_X]`. Distinguish the cases in `hβ : Finsupp.single k 1 = β`. Rewrite `hn` using `[if_pos hβ]`. Take `rfl` from `eq_zero_of_mem_support_one hn`.

Substitute `hβ` using the available equality. Use `⟨?_, by simp [Finsupp.degree_single]⟩` and prove the remaining obligations. Use `first`. Consider the case `exact zero_le _`. Consider the case `exact fun i => Nat.zero_le _`.

Consider the case `simp`. Rewrite `hn` using `[if_neg hβ]`. Simplify using `at hn`.
-/
private theorem biLe_single_one_X (x : ι) (k : κ) :
    BiLe (Finsupp.single x 1) (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n hn
  rw [MvPolynomial.coeff_X] at hn
  by_cases hβ : Finsupp.single k 1 = β
  · rw [if_pos hβ] at hn
    obtain rfl := eq_zero_of_mem_support_one hn
    subst hβ
    refine ⟨?_, by simp [Finsupp.degree_single]⟩
    first
      | exact zero_le _
      | exact fun i => Nat.zero_le _
      | simp
  · rw [if_neg hβ] at hn
    simp at hn

/- English proof (translation)
Establish `h` using `biLe_mul (biLe_CC (ι := ι) (κ := κ) a) (biLe_single_one_X (K := K) x k)`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis.
-/
lemma biLe_CC_mul_X (x : ι) (a : K) (k : κ) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.C a) * MvPolynomial.X k :
      MvPolynomial κ (MvPolynomial ι K)) := by
  have h := biLe_mul (biLe_CC (ι := ι) (κ := κ) a) (biLe_single_one_X (K := K) x k)
  rwa [zero_add] at h

/- English proof (translation)
The claim follows from `biLe_add (biLe_CX x) (biLe_sum _ _ (fun k _ => biLe_CC_mul_X x (b k x) k))`.
-/
lemma biLe_gen [Fintype κ] (b : κ → ι → K) (x : ι) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.X x) +
      ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
        MvPolynomial κ (MvPolynomial ι K)) :=
  biLe_add (biLe_CX x) (biLe_sum _ _ (fun k _ => biLe_CC_mul_X x (b k x) k))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, Finsupp.single_zero]`. Conclude with `biLe_one`. Consider the case `succ m ih => rw [pow_succ, Finsupp.single_add]`. Conclude with `biLe_mul ih h`.
-/
lemma biLe_pow_single {x : ι} {W : MvPolynomial κ (MvPolynomial ι K)}
    (h : BiLe (Finsupp.single x 1) W) (m : ℕ) : BiLe (Finsupp.single x m) (W ^ m) := by
  induction m with
  | zero => rw [pow_zero, Finsupp.single_zero]; exact biLe_one
  | succ m ih => rw [pow_succ, Finsupp.single_add]; exact biLe_mul ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.prod_empty]`. Conclude with `biLe_one`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`.

Conclude with `biLe_mul (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))`.
-/
lemma biLe_prod {α : Type*} (s : Finset α) (N : α → ι →₀ ℕ)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe (N a) (W a)) :
    BiLe (∑ a ∈ s, N a) (∏ a ∈ s, W a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact biLe_one
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact biLe_mul (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/- English proof (translation)
Rewrite using `[shiftPoly, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]`. Use `Finset.sum_congr rfl (fun n0 _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`.
-/
lemma shiftPoly_eq_sum [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = ∑ n0 ∈ Q.support, MvPolynomial.C (MvPolynomial.C (MvPolynomial.coeff n0 Q)) *
      ∏ x ∈ n0.support, (MvPolynomial.C (MvPolynomial.X x) +
        ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
          MvPolynomial κ (MvPolynomial ι K)) ^ n0 x := by
  rw [shiftPoly, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl (fun n0 _ => ?_)
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

end BiLe

/- English proof (translation)
Introduce `K ι κ _ _ b β Q n hn`. Express the relevant statement in the definitionally equal form `n ∈ (MvPolynomial.coeff β (shiftPoly b Q)).support at hn`. Rewrite `hn` using `[shiftPoly_eq_sum, MvPolynomial.coeff_sum, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]`. Take `⟨n0, hn0, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hn`. Establish `hs : ∑ x ∈ n0.support, Finsupp.single x (n0 x) = n0` using `Finsupp.sum_single n0`.

Establish `h` using `biLe_mul (biLe_CC (ι := ι) (κ := κ) (MvPolynomial.coeff n0 Q)) (biLe_prod n0.support (fun x => Finsupp.single x (n0 x)) _ (fun x _ => biLe_pow_single (biLe_gen b x) (n0 x)))`. Simplify using `only [zero_add, hs] at h`. Take `⟨h1, h2⟩` from `h β n (MvPolynomial.mem_support_iff.mpr hne)`. Use `⟨n0, hn0, h1, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[Finsupp.degree_eq_sum β]`. Then use the resulting hypothesis.
-/
theorem hasseDerivSupport : HasseDegree := by
  intro K ι κ _ _ b β Q n hn
  classical
  change n ∈ (MvPolynomial.coeff β (shiftPoly b Q)).support at hn
  rw [shiftPoly_eq_sum, MvPolynomial.coeff_sum, MvPolynomial.mem_support_iff,
    MvPolynomial.coeff_sum] at hn
  obtain ⟨n0, hn0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hs : ∑ x ∈ n0.support, Finsupp.single x (n0 x) = n0 := Finsupp.sum_single n0
  have h := biLe_mul (biLe_CC (ι := ι) (κ := κ) (MvPolynomial.coeff n0 Q))
    (biLe_prod n0.support (fun x => Finsupp.single x (n0 x)) _
      (fun x _ => biLe_pow_single (biLe_gen b x) (n0 x)))
  simp only [zero_add, hs] at h
  obtain ⟨h1, h2⟩ := h β n (MvPolynomial.mem_support_iff.mpr hne)
  refine ⟨n0, hn0, h1, ?_⟩
  rwa [Finsupp.degree_eq_sum β] at h2

section PosDeg

variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}

def posWt (r0 r1 : ℕ) (s : σ) : σ × Fin r0 × Fin r1 → ℕ := fun x => if x.1 = s then 1 else 0

/- English proof (translation)
Establish `hinj : Set.InjOn (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)) ((Finset.univ : Finset (Fin r0 × Fin r1)) : Set (Fin r0 × Fin r1))` using `fun x _ y _ h => by simpa using h`. Establish `hsub : n.support ⊆ n.support ∪ Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1))` using `fun i hi => Finset.mem_union_left _ hi`. Rewrite using `[Finsupp.weight_apply]`. Use `(Finsupp.sum_of_support_subset n hsub (fun i c => c • posWt r0 r1 s i) ?hz).trans ?hs` and prove the remaining obligations. Use `case hz =>`.

Introduce `i _`. Use `first`. Consider the case `exact zero_smul ℕ _`. Consider the case `simp`. Use `case hs =>`.

Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_subset (fun i hi => Finset.mem_union_right _ hi) ?_).symm` and prove the remaining obligations. Introduce `i _ hi`. Establish `hne : i.1 ≠ s`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[Finset.mem_image]`. Conclude with `⟨i.2, Finset.mem_univ _, by rw [← h]⟩`. Simplify using `[posWt, hne]`. Use `_ = ∑ x : Fin r0 × Fin r1, n (s, x) • posWt r0 r1 s (s, x) := Finset.sum_image hinj`.

Use `_ = ∑ x : Fin r0 × Fin r1, n (s, x) := by simp [posWt]`.
-/
lemma weight_posWt (s : σ) (n : σ × Fin r0 × Fin r1 →₀ ℕ) :
    Finsupp.weight (posWt r0 r1 s) n = ∑ x : Fin r0 × Fin r1, n (s, x) := by
  classical
  have hinj : Set.InjOn (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1))
      ((Finset.univ : Finset (Fin r0 × Fin r1)) : Set (Fin r0 × Fin r1)) :=
    fun x _ y _ h => by simpa using h
  have hsub : n.support ⊆ n.support ∪
      Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)) :=
    fun i hi => Finset.mem_union_left _ hi
  rw [Finsupp.weight_apply]
  refine (Finsupp.sum_of_support_subset n hsub (fun i c => c • posWt r0 r1 s i) ?hz).trans ?hs
  case hz =>
    intro i _
    first
      | exact zero_smul ℕ _
      | simp
  case hs =>
    calc ∑ i ∈ n.support ∪ Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)),
          n i • posWt r0 r1 s i
        = ∑ i ∈ Finset.univ.image (fun x : Fin r0 × Fin r1 => ((s, x) : σ × Fin r0 × Fin r1)),
          n i • posWt r0 r1 s i := by
          refine (Finset.sum_subset (fun i hi => Finset.mem_union_right _ hi) ?_).symm
          intro i _ hi
          have hne : i.1 ≠ s := by
            intro h
            apply hi
            rw [Finset.mem_image]
            exact ⟨i.2, Finset.mem_univ _, by rw [← h]⟩
          simp [posWt, hne]
      _ = ∑ x : Fin r0 × Fin r1, n (s, x) • posWt r0 r1 s (s, x) := Finset.sum_image hinj
      _ = ∑ x : Fin r0 × Fin r1, n (s, x) := by simp [posWt]

/- English proof (translation)
Apply the tactic sequence `have hdeg : (if s' = s then l else 0) = 0 + ∑ _i : Fin l, (if s' = s then 1 else 0) := by split_ifs with h <;> simp [h]`. Rewrite using `[hdeg, minorAt, Matrix.det_apply']`. Use `MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun e _ => ?_)` and prove the remaining obligations. Use `MvPolynomial.IsWeightedHomogeneous.mul ?hsign (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?hent))` and prove the remaining obligations. Use `case hsign =>`.

Establish `hC` using `MvPolynomial.isWeightedHomogeneous_C (posWt r0 r1 s) ((Equiv.Perm.sign e : ℤ) : K)`. Rewrite `hC` using `[map_intCast]`. Conclude with `hC`. Use `case hent => show MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s) (∑ a, MvPolynomial.C (T (e i) a) * MvPolynomial.X (s', a, I i)) (if s' = s then 1 else 0)`. Use `MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)` and prove the remaining obligations.

Conclude with `(MvPolynomial.isWeightedHomogeneous_X K (posWt r0 r1 s) (s', a, I i)).C_mul (T (e i) a)`.
-/
lemma minorAt_posWt {l : ℕ} (s s' : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s) (minorAt s' T I)
      (if s' = s then l else 0) := by
  have hdeg : (if s' = s then l else 0) = 0 + ∑ _i : Fin l, (if s' = s then 1 else 0) := by
    split_ifs with h <;> simp [h]
  rw [hdeg, minorAt, Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun e _ => ?_)
  refine MvPolynomial.IsWeightedHomogeneous.mul ?hsign
    (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?hent))
  case hsign =>
    have hC := MvPolynomial.isWeightedHomogeneous_C (posWt r0 r1 s)
      ((Equiv.Perm.sign e : ℤ) : K)
    rw [map_intCast] at hC
    exact hC
  case hent =>
    show MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s)
      (∑ a, MvPolynomial.C (T (e i) a) * MvPolynomial.X (s', a, I i)) (if s' = s then 1 else 0)
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
    exact (MvPolynomial.isWeightedHomogeneous_X K (posWt r0 r1 s) (s', a, I i)).C_mul (T (e i) a)

end PosDeg

/- English proof (translation)
Introduce `K σ _ _ r0 r1 C l sf T I n hn s`. Establish `hH` using `MvPolynomial.IsWeightedHomogeneous.prod Finset.univ (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s then l c else 0) (w := posWt r0 r1 s) (fun c _ => minorAt_posWt s (sf c) (T c) (I c))`. Establish `h` using `hH (MvPolynomial.mem_support_iff.mp hn)`. Rewrite `h` using `[weight_posWt]`. Rewrite using `[h, Finset.sum_filter]`.
-/
theorem minorProdBlockDegree : MinorProdDegree := by
  intro K σ _ _ r0 r1 C l sf T I n hn s
  have hH := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s then l c else 0)
    (w := posWt r0 r1 s) (fun c _ => minorAt_posWt s (sf c) (T c) (I c))
  have h := hH (MvPolynomial.mem_support_iff.mp hn)
  rw [weight_posWt] at h
  rw [h, Finset.sum_filter]

end Formalism.InvariantFactorPaths.G7
