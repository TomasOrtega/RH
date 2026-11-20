import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData

open Finset

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise S b]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => ((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)]`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Introduce `p hp`.

Rewrite using `[(Finset.mem_filter.mp hp).2]`.
-/
theorem count_rhs :
    (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) := by
  rw [← Finset.sum_fiberwise S b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)]
  · rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

/- English proof (translation)
Establish `hc : (S.filter fun q => col q = col p ∧ b p < b q).card = (Finset.Ioi (b p)).card`. Apply `Finset.card_bij (fun q _ => b q)` to reduce the goal to its premises. Introduce `q hq`. Simplify using `only [Finset.mem_filter] at hq`. Conclude with `Finset.mem_Ioi.mpr hq.2.2`.

Introduce `q₁ h₁ q₂ h₂ h`. Simplify using `only [Finset.mem_filter] at h₁ h₂`. Conclude with `hT.1 q₁ q₂ (h₁.2.1.trans h₂.2.1.symm) h`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ioi]`.

Take `⟨q, hq1, hq2⟩` from `hT.2 p i hi`. Use `⟨q, ?_, hq2⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter]`. Use `⟨(hS q p hq1).2 hp, hq1, ?_⟩` and prove the remaining obligations. Rewrite using `[hq2]`.

Conclude with `hi`. Rewrite using `[hc, Fin.card_Ioi]`. Establish `h : (b p : ℕ) + 1 ≤ n` using `(b p).isLt`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega : 1 + (b p : ℕ) ≤ n)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem count_up (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => col q = col p ∧ b p < b q).card : ℝ) = n - 1 - (b p : ℕ) := by
  have hc : (S.filter fun q => col q = col p ∧ b p < b q).card = (Finset.Ioi (b p)).card := by
    apply Finset.card_bij (fun q _ => b q)
    · intro q hq
      simp only [Finset.mem_filter] at hq
      exact Finset.mem_Ioi.mpr hq.2.2
    · intro q₁ h₁ q₂ h₂ h
      simp only [Finset.mem_filter] at h₁ h₂
      exact hT.1 q₁ q₂ (h₁.2.1.trans h₂.2.1.symm) h
    · intro i hi
      rw [Finset.mem_Ioi] at hi
      obtain ⟨q, hq1, hq2⟩ := hT.2 p i hi
      refine ⟨q, ?_, hq2⟩
      simp only [Finset.mem_filter]
      refine ⟨(hS q p hq1).2 hp, hq1, ?_⟩
      rw [hq2]
      exact hi
  rw [hc, Fin.card_Ioi]
  have h : (b p : ℕ) + 1 ≤ n := (b p).isLt
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (b p : ℕ) ≤ n)]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Finset.sum_boole]`. Establish `h1 : (S.filter fun q => b q = b p).filter (fun q => col q = col p) = {p}`. Use extensionality with `q`. Simplify using `only [Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, h2⟩, h3⟩`. Conclude with `hT.1 q p h3 h2`. Introduce and unpack `rfl`. Conclude with `⟨⟨hp, rfl⟩, rfl⟩`. Establish `h2 : (S.filter fun q => b q = b p).filter (fun q => ¬ col q = col p) = S.filter (fun q => col q ≠ col p ∧ b q = b p)`.

Use extensionality with `q`. Simplify using `only [Finset.mem_filter]`. The claim follows by propositional logic. Establish `h3` using `Finset.card_filter_add_card_filter_not (s := S.filter fun q => b q = b p) (fun q => col q = col p)`. Use `beta_reduce at h3`.

Rewrite `h3` using `[h1, h2, Finset.card_singleton]`. Rewrite using `[← h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem count_eqb (hT : IsTab col b) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => b q = b p).card : ℝ) =
      1 + ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have h1 : (S.filter fun q => b q = b p).filter (fun q => col q = col p) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact hT.1 q p h3 h2
    · rintro rfl
      exact ⟨⟨hp, rfl⟩, rfl⟩
  have h2 : (S.filter fun q => b q = b p).filter (fun q => ¬ col q = col p) =
      S.filter (fun q => col q ≠ col p ∧ b q = b p) := by
    ext q
    simp only [Finset.mem_filter]
    tauto
  have h3 := Finset.card_filter_add_card_filter_not (s := S.filter fun q => b q = b p)
    (fun q => col q = col p)
  beta_reduce at h3
  rw [h1, h2, Finset.card_singleton] at h3
  rw [← h3]
  push_cast
  ring

/- English proof (translation)
Establish `hpt : ∀ p q : Q, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) = (if col q = col p ∧ b p < b q then 1 else 0) + (if col p = col q ∧ b q < b p then 1 else 0)`. Introduce `p q`. Distinguish the cases in `hc : col q = col p`. Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality.

Simplify using the standard rewrite rules. Establish `hb : b q ≠ b p` using `fun hb => hq (hT.1 q p hc hb)`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Simplify using `[hc, hq, h, not_lt.mpr h.le]`. Simplify using `[hc, hq, h, not_lt.mpr h.le]`.

Establish `hc' : col p ≠ col q` using `fun h => hc h.symm`. Simplify using `[hc, hc']`. Repeatedly rewrite using `[hpt, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun p q => if col p = col q ∧ b q < b p then (1 : ℝ) else 0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem count_same (hT : IsTab col b) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      2 * ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1 : ℝ) else 0) := by
  have hpt : ∀ p q : Q, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      (if col q = col p ∧ b p < b q then 1 else 0) + (if col p = col q ∧ b q < b p then 1 else 0) := by
    intro p q
    by_cases hc : col q = col p
    · by_cases hq : q = p
      · subst hq; simp
      · have hb : b q ≠ b p := fun hb => hq (hT.1 q p hc hb)
        rcases lt_or_gt_of_ne hb with h | h
        · simp [hc, hq, h, not_lt.mpr h.le]
        · simp [hc, hq, h, not_lt.mpr h.le]
    · have hc' : col p ≠ col q := fun h => hc h.symm
      simp [hc, hc']
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun p q => if col p = col q ∧ b q < b p then (1 : ℝ) else 0)]
  ring

end

end PositivityTheory.Rg.Cz
