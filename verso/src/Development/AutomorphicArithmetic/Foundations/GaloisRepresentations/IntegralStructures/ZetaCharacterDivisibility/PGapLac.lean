import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj

noncomputable section

open GlobalTheory.RoadWGeo GlobalTheory.CongL

namespace UpperTheory.Gal.Int.Div

/- English proof (translation)
Rewrite using `[Finset.orderEmbOfFin_apply]`. Establish `hl : i < (J.val.sort (· ≤ ·)).length`. Simplify `hi` using `[hcard]`. Rewrite using `[List.getD_eq_getElem _ _ hl]`. Both sides reduce to the same expression.
-/
private theorem getD_eq (J : Finset ℤ) (a : ℕ) (hcard : J.card = a) (i : ℕ) (hi : i < a) :
    (J.val.sort (· ≤ ·)).getD i 0 = J.orderEmbOfFin hcard ⟨i, hi⟩ := by
  rw [Finset.orderEmbOfFin_apply]
  have hl : i < (J.val.sort (· ≤ ·)).length := by
    simpa [hcard] using hi
  rw [List.getD_eq_getElem _ _ hl]
  rfl

/- English proof (translation)
Simplify using `[Finset.sum_sub_distrib]`.
-/
private theorem sum_shift (A : Finset ℤ) (c : ℤ) : ∑ x ∈ A, (x - c) = A.sum id - (A.card : ℤ) * c := by
  simp [Finset.sum_sub_distrib]

/- English proof (translation)
Establish `h1 : m - c ≤ ∑ x ∈ A, (x - c)` using `Finset.single_le_sum (f := fun x => x - c) (fun x hx => sub_nonneg.2 (hmin x (hA hx))) hm`. Establish `hc : (A.card : ℤ) ≤ J.card` using `by exact_mod_cast Finset.card_le_card hA`. Establish `h2 : ∑ b ∈ B, (A.card : ℤ) * (b - c) < ∑ _b ∈ B, (m - c)`. Use `Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_` and prove the remaining obligations. Establish `h3` using `hg b (hB hb) m (hA hm) (hlt b hb)`.

Establish `h4` using `mul_le_mul_of_nonneg_right hc (sub_nonneg.2 (hmin b (hB hb)))`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h2` using `[← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, sum_shift]`. Rewrite `h1` using `[sum_shift]`. Establish `h5 : (B.card : ℤ) * (m - c) ≤ B.card * (A.sum id - (A.card : ℤ) * c)` using `mul_le_mul_of_nonneg_left h1 (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem avg_lt {J A B : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) (hA : A ⊆ J) (hB : B ⊆ J)
    (hBn : B.Nonempty) {m : ℤ} (hm : m ∈ A) (hlt : ∀ b ∈ B, b < m) :
    (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
  have h1 : m - c ≤ ∑ x ∈ A, (x - c) :=
    Finset.single_le_sum (f := fun x => x - c) (fun x hx => sub_nonneg.2 (hmin x (hA hx))) hm
  have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
  have h2 : ∑ b ∈ B, (A.card : ℤ) * (b - c) < ∑ _b ∈ B, (m - c) := by
    refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
    have h3 := hg b (hB hb) m (hA hm) (hlt b hb)
    have h4 := mul_le_mul_of_nonneg_right hc (sub_nonneg.2 (hmin b (hB hb)))
    linarith
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, sum_shift] at h2
  rw [sum_shift] at h1
  have h5 : (B.card : ℤ) * (m - c) ≤ B.card * (A.sum id - (A.card : ℤ) * c) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/- English proof (translation)
Introduce `A B hA hB hd hAn hBn`. Establish `hne : (A ∪ B).Nonempty` using `hAn.mono Finset.subset_union_left`. Establish `hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne` using `fun x hx => Finset.le_max' _ _ hx`. Break down `Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm` into its components or cases. Use `(avg_lt hmin hg hA hB hBn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'` and prove the remaining obligations.

Introduce `e`. Conclude with `Finset.disjoint_left.1 hd hm (e ▸ hb)`. Use `(avg_lt hmin hg hB hA hAn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne` and prove the remaining obligations. Introduce `e`. Conclude with `Finset.disjoint_left.1 hd hb (e ▸ hm)`.
-/
private theorem lacunary_of_shift {J : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) : Lacunary J := by
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (avg_lt hmin hg hA hB hBn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (avg_lt hmin hg hB hA hAn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

/- English proof (translation)
Introduce `a J hcard hgap`. Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases. Substitute `ha` using the available equality. Establish `hJ : J = ∅` using `Finset.card_eq_zero.1 hcard`. Substitute `hJ` using the available equality.

Conclude with `lacunary_of_shift (c := 0) (by simp) (by simp)`. Establish `hmem : ∀ x ∈ J, ∃ i, J.orderEmbOfFin hcard i = x`. Introduce `x hx`. Establish `: x ∈ Set.range (J.orderEmbOfFin hcard)`. Rewrite using `[Finset.range_orderEmbOfFin]`.

Conclude with `hx`. Conclude with `this`. Use `lacunary_of_shift (c := J.orderEmbOfFin hcard ⟨0, ha⟩) (fun x hx => ?_) fun x hx y hy hxy => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `hmem x hx`. Conclude with `(J.orderEmbOfFin hcard).monotone (Fin.mk_le_of_le_val (Nat.zero_le _))`.

Take `⟨i, rfl⟩` from `hmem x hx`. Take `⟨j, rfl⟩` from `hmem y hy`. Establish `hij : i < j` using `(J.orderEmbOfFin hcard).lt_iff_lt.1 hxy`. Take `⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1` from `⟨(j : ℕ) - 1, by have : (i : ℕ) < j := hij; omega⟩`. Establish `hk1 : k + 1 < a` using `hk ▸ j.2`.

Establish `hk0 : k < a` using `by omega`. Establish `hjk : j = ⟨k + 1, hk1⟩` using `Fin.ext hk`. Establish `hg` using `hgap k hk1`. Rewrite `hg` using `[getD_eq J a hcard (k + 1) hk1, getD_eq J a hcard 0 ha, getD_eq J a hcard k hk0]`. Establish `hik : J.orderEmbOfFin hcard i ≤ J.orderEmbOfFin hcard ⟨k, hk0⟩` using `(J.orderEmbOfFin hcard).monotone (by`.

Establish `: (i : ℕ) < j` using `hij`. Use `show (i : ℕ) ≤ k`. Use the proof step `omega)`. Rewrite using `[hcard, hjk]`. Establish `h6` using `mul_le_mul_of_nonneg_left (sub_le_sub_right hik (J.orderEmbOfFin hcard ⟨0, ha⟩)) (Int.natCast_nonneg a)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gapLac_of : GapLac := by
  intro a J hcard hgap
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hJ : J = ∅ := Finset.card_eq_zero.1 hcard
    subst hJ
    exact lacunary_of_shift (c := 0) (by simp) (by simp)
  have hmem : ∀ x ∈ J, ∃ i, J.orderEmbOfFin hcard i = x := by
    intro x hx
    have : x ∈ Set.range (J.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    exact this
  refine lacunary_of_shift (c := J.orderEmbOfFin hcard ⟨0, ha⟩) (fun x hx => ?_) fun x hx y hy hxy => ?_
  · obtain ⟨i, rfl⟩ := hmem x hx
    exact (J.orderEmbOfFin hcard).monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
  · obtain ⟨i, rfl⟩ := hmem x hx
    obtain ⟨j, rfl⟩ := hmem y hy
    have hij : i < j := (J.orderEmbOfFin hcard).lt_iff_lt.1 hxy
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by have : (i : ℕ) < j := hij; omega⟩
    have hk1 : k + 1 < a := hk ▸ j.2
    have hk0 : k < a := by omega
    have hjk : j = ⟨k + 1, hk1⟩ := Fin.ext hk
    have hg := hgap k hk1
    rw [getD_eq J a hcard (k + 1) hk1, getD_eq J a hcard 0 ha, getD_eq J a hcard k hk0] at hg
    have hik : J.orderEmbOfFin hcard i ≤ J.orderEmbOfFin hcard ⟨k, hk0⟩ :=
      (J.orderEmbOfFin hcard).monotone (by
        have : (i : ℕ) < j := hij
        show (i : ℕ) ≤ k
        omega)
    rw [hcard, hjk]
    have h6 := mul_le_mul_of_nonneg_left (sub_le_sub_right hik (J.orderEmbOfFin hcard ⟨0, ha⟩))
      (Int.natCast_nonneg a)
    linarith

end UpperTheory.Gal.Int.Div

end
