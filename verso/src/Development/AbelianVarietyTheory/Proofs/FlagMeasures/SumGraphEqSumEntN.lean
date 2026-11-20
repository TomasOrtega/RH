import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

/- English proof (translation)
Establish `h1 : ∀ a : Fin N, (∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) = if (a : ℕ) ∈ S then entN M a (f a) else 0`. Introduce `a`. Distinguish the cases in `ha : (a : ℕ) ∈ S`. Rewrite using `[if_pos ha]`. Distinguish the cases in `hf : f a < N`.

Rewrite using `[Finset.sum_eq_single ⟨f a, hf⟩]`. Use `split_ifs with hc`. Unfold `entN`. Rewrite using `[dif_pos ⟨a.isLt, hf⟩]`. Conclude with `absurd ⟨ha, rfl⟩ hc`.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext h.2)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_zero]`. Unfold `entN`. Rewrite using `[dif_neg (fun hh => hf hh.2)]`. Introduce `b _`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hf (h.2 ▸ b.isLt)`. Rewrite using `[if_neg ha]`. Conclude with `Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1))`.

Rewrite using `[Finset.sum_congr rfl (fun a _ => h1 a)]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then entN M a (f a) else 0) N]`. Rewrite using `[← Finset.sum_filter]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `a ha`.

Conclude with `(Finset.mem_filter.mp ha).2`. Introduce `a haS hnot`. Establish `hlt : ¬ a < N` using `fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haS⟩)`. Unfold `entN`. Rewrite using `[dif_neg (fun hh => hlt hh.1)]`.
-/
theorem sum_graph_eq_sum_entN {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (S : Finset ℕ) (f : ℕ → ℕ) :
    (∑ a : Fin N, ∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      ∑ a ∈ S, entN M a (f a) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      if (a : ℕ) ∈ S then entN M a (f a) else 0 := by
    intro a
    by_cases ha : (a : ℕ) ∈ S
    · rw [if_pos ha]
      by_cases hf : f a < N
      · rw [Finset.sum_eq_single ⟨f a, hf⟩]
        · split_ifs with hc
          · unfold entN
            rw [dif_pos ⟨a.isLt, hf⟩]
          · exact absurd ⟨ha, rfl⟩ hc
        · intro b _ hb
          rw [if_neg]
          intro h
          exact hb (Fin.ext h.2)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero]
        · unfold entN
          rw [dif_neg (fun hh => hf hh.2)]
        · intro b _
          rw [if_neg]
          intro h
          exact hf (h.2 ▸ b.isLt)
    · rw [if_neg ha]
      exact Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1))
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then entN M a (f a) else 0) N]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a haS hnot
    have hlt : ¬ a < N := fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haS⟩)
    unfold entN
    rw [dif_neg (fun hh => hlt hh.1)]

/- English proof (translation)
Simplify using `only [phI, IsW, Fin.lt_iff_val_lt_val]`. Apply the tactic sequence `constructor <;> intro h <;> omega`.
-/
theorem phI_last_iff {N : ℕ} (k s : ℕ) (a b : Fin N) :
    phI k s s a b ↔ (a : ℕ) < b ∧ ¬ (s ≤ (a : ℕ) ∧ (a : ℕ) < s + k ∧ (b : ℕ) = s + k) := by
  simp only [phI, IsW, Fin.lt_iff_val_lt_val]
  constructor <;> intro h <;> omega

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `InPat IsUniUp`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun a b => ⟨fun hba => ?_, fun hab => ?_⟩, fun a h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hv` using `Fin.lt_iff_val_lt_val.mp hba`.

Establish `hn : ¬ phI k s s a b`. Rewrite using `[phI_last_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h a b hn, Matrix.one_apply_ne]`. Introduce `e`.

Rewrite `hv` using `[e]`. Use linear arithmetic over natural numbers and integers. Substitute `hab` using the available equality. Establish `hn : ¬ phI k s s a a`. Rewrite using `[phI_last_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h a a hn, Matrix.one_apply_eq]`. Unfold `entN split_ifs with hh`. Establish `hn : ¬ phI k s s (⟨a, hh.1⟩ : Fin N) ⟨s + k, hh.2⟩`. Rewrite using `[phI_last_iff]`.

Conclude with `fun h' => h'.2 ⟨h1, h2, rfl⟩`. Rewrite using `[h _ _ hn, Matrix.one_apply_ne]`. Introduce `e`. Simplify using `only [Fin.mk.injEq] at e`. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Introduce and unpack `⟨hU, hz⟩ ⟨a, ha⟩ ⟨b, hb⟩ hn`. Rewrite `hn` using `[phI_last_iff]`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Establish `hw : s ≤ a ∧ a < s + k ∧ b = s + k`.

Assume the negation of the conclusion as `hc`. Conclude with `hn ⟨hab, hc⟩`. Take `⟨hw1, hw2, rfl⟩` from `hw`. Establish `h0` using `hz a hw1 hw2`. Unfold `entN at h0`.

Rewrite `h0` using `[dif_pos ⟨ha, hb⟩]`. Rewrite using `[Matrix.one_apply_ne]`. Conclude with `h0`. Introduce `e`. Simplify using `only [Fin.mk.injEq] at e`.

Use linear arithmetic over natural numbers and integers. Substitute `hab` using the available equality. Rewrite using `[(hU _ _).2 rfl, Matrix.one_apply_eq]`. Rewrite using `[(hU _ _).1 (Fin.mk_lt_mk.mpr hab), Matrix.one_apply_ne]`. Introduce `e`.

Simplify using `only [Fin.mk.injEq] at e`. Use linear arithmetic over natural numbers and integers.
-/
theorem inPat_phI_last_iff {N : ℕ} (k s : ℕ) (M : Mt g N) :
    InPat (phI k s s) M ↔ IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 := by
  unfold InPat IsUniUp
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hba => ?_, fun hab => ?_⟩, fun a h1 h2 => ?_⟩
    · have hv := Fin.lt_iff_val_lt_val.mp hba
      have hn : ¬ phI k s s a b := by
        rw [phI_last_iff]
        omega
      rw [h a b hn, Matrix.one_apply_ne]
      intro e
      rw [e] at hv
      omega
    · subst hab
      have hn : ¬ phI k s s a a := by
        rw [phI_last_iff]
        omega
      rw [h a a hn, Matrix.one_apply_eq]
    · unfold entN
      split_ifs with hh
      · have hn : ¬ phI k s s (⟨a, hh.1⟩ : Fin N) ⟨s + k, hh.2⟩ := by
          rw [phI_last_iff]
          exact fun h' => h'.2 ⟨h1, h2, rfl⟩
        rw [h _ _ hn, Matrix.one_apply_ne]
        intro e
        simp only [Fin.mk.injEq] at e
        omega
      · rfl
  · rintro ⟨hU, hz⟩ ⟨a, ha⟩ ⟨b, hb⟩ hn
    rw [phI_last_iff] at hn
    rcases lt_trichotomy a b with hab | hab | hab
    · have hw : s ≤ a ∧ a < s + k ∧ b = s + k := by
        by_contra hc
        exact hn ⟨hab, hc⟩
      obtain ⟨hw1, hw2, rfl⟩ := hw
      have h0 := hz a hw1 hw2
      unfold entN at h0
      rw [dif_pos ⟨ha, hb⟩] at h0
      rw [Matrix.one_apply_ne]
      · exact h0
      · intro e
        simp only [Fin.mk.injEq] at e
        omega
    · subst hab
      rw [(hU _ _).2 rfl, Matrix.one_apply_eq]
    · rw [(hU _ _).1 (Fin.mk_lt_mk.mpr hab), Matrix.one_apply_ne]
      intro e
      simp only [Fin.mk.injEq] at e
      omega

/- English proof (translation)
Rewrite using `[← sum_graph_eq_sum_entN]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Distinguish the cases in `hp : P a b`. Rewrite using `[if_pos hp, if_pos ((h a b b.isLt).1 hp)]`. Rewrite using `[if_neg hp, if_neg (fun hq => hp ((h a b b.isLt).2 hq))]`.
-/
private theorem sum_sum_ite_eq_sum_entN_of_iff {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)] (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ a b : ℕ, b < N → (P a b ↔ a ∈ S ∧ b = f a)) :
    (∑ a : Fin N, ∑ b : Fin N, if P (a : ℕ) (b : ℕ) then M a b else 0) = ∑ a ∈ S, entN M a (f a) := by
  rw [← sum_graph_eq_sum_entN]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hp : P a b
  · rw [if_pos hp, if_pos ((h a b b.isLt).1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp ((h a b b.isLt).2 hq))]

/- English proof (translation)
Substitute `hN` using the available equality. Establish `hsplit : sumAt (eeI k s) M = (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) + (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) + (∑ a : Fin (k + 2 * s + 1), ∑ …`. Unfold `sumAt`. Simplify using `only [← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations.

Establish `hb` using `b.isLt`. Unfold `eeI IsW`. Apply the tactic sequence `split_ifs <;> first | omega | simp`. Apply the tactic sequence `have h1 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) = ∑ a ∈ Finset.range (s - 1), entN M a (a + 1) := sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ b < s) _ (fun a => a + 1) (fun a b _ => by simp only [Fi …`. Apply the tactic sequence `have h2 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) = ∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k) := sum_sum_ite_eq_sum_entN_of_iff M (fun a b => a + 1 = s ∧ b = s + k) _ (fun _ => s + k …`.

Establish `h3 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) = ∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)`. Apply the tactic sequence `rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s + k ≤ a) (Finset.Ico (s + k) (s + k + s)) (fun a => a + 1) (fun a b hb => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]`. Rewrite using `[Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]`. Establish `h4 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1), if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) = ∑ a ∈ Finset.range (k - 1), entN M (s + a) (s + a + 1)`. Apply the tactic sequence `rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s ≤ a ∧ b < s + k) (Finset.Ico s (s + (k - 1))) (fun a => a + 1) (fun a b _ => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]`.

Rewrite using `[Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]`. Establish `key : (∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k)) + (∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)) = (if 1 ≤ s then entN M (s - 1) (s + k) + entN M (s + k) (s + k + 1) else 0) + ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + …`. Break down `Nat.eq_zero_or_pos s with hs | hs` into its components or cases. Substitute `hs` using the available equality. Simplify using the standard rewrite rules.

Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`. Establish `hB : (Finset.range (t + 1)).filter (fun a => a + 1 = t + 1) = {t}`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]`. Use linear arithmetic over natural numbers and integers.

Establish `hC : (∑ i ∈ Finset.range (t + 1), entN M (t + 1 + k + i) (t + 1 + k + i + 1)) = (∑ i ∈ Finset.range (t + 1 - 1), entN M (t + 1 + k + 1 + i) (t + 1 + k + 2 + i)) + entN M (t + 1 + k) (t + 1 + k + 1)`. Rewrite using `[Finset.sum_range_succ', Nat.add_sub_cancel]`. Simplify using `only [add_zero]`. Use `congr 1`. Apply the tactic sequence `exact Finset.sum_congr rfl (fun i _ => by congr 1 <;> omega)`.

Rewrite using `[hB, Finset.sum_singleton, hC, if_pos (show 1 ≤ t + 1 by omega), Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, h1, h2, h3, h4]`. Unfold `phiJ`. Take the linear combination `key`.
-/
theorem sumAt_eeI_eq_phiJ {N : ℕ} (k s : ℕ) (hN : N = k + 2 * s + 1) (M : Mt g N) :
    sumAt (eeI k s) M = phiJ k s M := by
  subst hN
  have hsplit : sumAt (eeI k s) M =
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) := by
    unfold sumAt
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hb := b.isLt
    unfold eeI IsW
    split_ifs <;> first | omega | simp
  have h1 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) =
      ∑ a ∈ Finset.range (s - 1), entN M a (a + 1) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ b < s) _ (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_range]; constructor <;> intro h <;> omega)
  have h2 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) =
      ∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => a + 1 = s ∧ b = s + k) _ (fun _ => s + k)
      (fun a b _ => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> omega)
  have h3 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) =
      ∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s + k ≤ a) (Finset.Ico (s + k) (s + k + s)) (fun a => a + 1)
      (fun a b hb => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h4 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) =
      ∑ a ∈ Finset.range (k - 1), entN M (s + a) (s + a + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s ≤ a ∧ b < s + k) (Finset.Ico s (s + (k - 1))) (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have key : (∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k)) +
      (∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)) =
      (if 1 ≤ s then entN M (s - 1) (s + k) + entN M (s + k) (s + k + 1) else 0) +
      ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have hB : (Finset.range (t + 1)).filter (fun a => a + 1 = t + 1) = {t} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      have hC : (∑ i ∈ Finset.range (t + 1), entN M (t + 1 + k + i) (t + 1 + k + i + 1)) =
          (∑ i ∈ Finset.range (t + 1 - 1), entN M (t + 1 + k + 1 + i) (t + 1 + k + 2 + i)) +
            entN M (t + 1 + k) (t + 1 + k + 1) := by
        rw [Finset.sum_range_succ', Nat.add_sub_cancel]
        simp only [add_zero]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by congr 1 <;> omega)
      rw [hB, Finset.sum_singleton, hC, if_pos (show 1 ≤ t + 1 by omega), Nat.add_sub_cancel]
      ring
  rw [hsplit, h1, h2, h3, h4]
  unfold phiJ
  linear_combination key

/- English proof (translation)
Introduce `g _ ψ N k s hN`. Establish `hP : (InPat (phI k s s) : Mt g N → Prop) = fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0`. Use function extensionality and compare the values at `fun M => propext (inPat_phI_last_iff k s M)`. Establish `hφ : (sumAt (eeI k s) : Mt g N → ZMod g) = phiJ k s` using `funext fun M => sumAt_eeI_eq_phiJ k s hN M`. Unfold `ePat eJ`.

Rewrite using `[hP, hφ]`.
-/
theorem ePat_last_eq_eJ : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ePat g N (phI k s s) (eeI k s) ψ = eJ g N k s ψ := by
  intro g _ ψ N k s hN
  have hP : (InPat (phI k s s) : Mt g N → Prop) =
      fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 :=
    funext fun M => propext (inPat_phI_last_iff k s M)
  have hφ : (sumAt (eeI k s) : Mt g N → ZMod g) = phiJ k s := funext fun M => sumAt_eeI_eq_phiJ k s hN M
  unfold ePat eJ
  rw [hP, hφ]

end GlobalTheory.GLm
