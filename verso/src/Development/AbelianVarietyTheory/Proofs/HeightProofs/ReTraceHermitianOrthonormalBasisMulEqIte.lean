import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.PB

variable {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality. Rewrite using `[unitE, unitE, Matrix.single_mul_single_same, one_mul]`. Distinguish the cases in `hda : d = a`. Substitute `hda` using the available equality.

Simplify using `[Matrix.trace_single_eq_same]`. Rewrite using `[Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]`. Simplify using `[hda]`. Rewrite using `[unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]`. Simplify using `[hbc]`.
-/
theorem tr_unit (a b c d : Fin n) :
    trace (unitE a b * unitE c d) = if b = c ∧ d = a then 1 else 0 := by
  by_cases hbc : b = c
  · subst hbc
    rw [unitE, unitE, Matrix.single_mul_single_same, one_mul]
    by_cases hda : d = a
    · subst hda; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]; simp [hda]
  · rw [unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp [hbc]

/- English proof (translation)
Rewrite using `[invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_inv : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

def B (X Y : Mx n) : ℝ := (trace (X * Y)).re

/- English proof (translation)
Simplify using `only [B, Matrix.trace_mul_comm X Y]`.
-/
theorem B_comm (X Y : Mx n) : B X Y = B Y X := by
  simp only [B, Matrix.trace_mul_comm X Y]

def f (p : Fin n × Fin n) : List (Mx n) :=
  [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pList_eq (ε : Fin n → Bool) : pList ε = (pairs ε false).flatMap f := rfl

/- English proof (translation)
Simplify using `only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h`. Conclude with `h.2.1`.
-/
theorem mem_pairs' {ε : Fin n → Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε false) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

/- English proof (translation)
The claim follows from `(List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _`.
-/
theorem nodup_pairs (ε : Fin n → Bool) : (pairs ε false).Nodup :=
  (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _

/- English proof (translation)
Establish `h1 : a ≠ b` using `hab.ne`. Establish `h2 : b ≠ a` using `hab.ne'`. Introduce `X hX`. Simplify using `only [f, List.mem_cons, List.not_mem_nil, or_false] at hX`. Break down `hX with rfl | rfl` into its components or cases.

Simplify using `only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit, h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]`. Evaluate the numerical expressions. Simplify using `only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit, h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]`. Establish `: invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ)`. Rewrite using `[show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring, sq_inv, Complex.I_mul_I]; ring`.

Rewrite using `[this]`. Evaluate the numerical expressions.
-/
theorem norm_one {a b : Fin n} (hab : a < b) : ∀ X ∈ f (a, b), B X X = 1 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  intro X hX
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]
    norm_num
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
    have : invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ) := by
      rw [show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring,
        sq_inv, Complex.I_mul_I]; ring
    rw [this]; norm_num

/- English proof (translation)
Establish `h1 : a ≠ b` using `hab.ne`. Establish `h2 : b ≠ a` using `hab.ne'`. Simplify using `only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]`. Simplify using `only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit, h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]`. Simplify using the standard rewrite rules.
-/
theorem within {a b : Fin n} (hab : a < b) : (f (a, b)).Pairwise fun X Y => B X Y = 0 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  simp only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit,
    h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  simp

/- English proof (translation)
Establish `e1 : ¬ (b = c ∧ d = a)` using `by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd`. Establish `e2 : ¬ (b = d ∧ c = a)` using `by rintro ⟨rfl, rfl⟩; exact hne rfl`. Establish `e3 : ¬ (a = c ∧ d = b)` using `by rintro ⟨rfl, rfl⟩; exact hne rfl`. Establish `e4 : ¬ (a = d ∧ c = b)` using `by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd`. Introduce `X hX Y hY`.

Simplify using `only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY`. Apply the tactic sequence `rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>`. Simplify using `only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]`.
-/
theorem across {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∀ X ∈ f (a, b), ∀ Y ∈ f (c, d), B X Y = 0 := by
  have e1 : ¬ (b = c ∧ d = a) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  have e2 : ¬ (b = d ∧ c = a) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e3 : ¬ (a = c ∧ d = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e4 : ¬ (a = d ∧ c = b) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  intro X hX Y hY
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub,
    Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]

/- English proof (translation)
Rewrite using `[pList_eq, List.pairwise_flatMap]`. Use `⟨fun p hp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `p`. Conclude with `within (mem_pairs' hp)`. Use `(nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_` and prove the remaining obligations.

Take `⟨a, b⟩` from `p`. Take `⟨c, d⟩` from `q`. Conclude with `across (mem_pairs' hp) (mem_pairs' hq) hne`.
-/
theorem pairwise_pList (ε : Fin n → Bool) : (pList ε).Pairwise fun X Y => B X Y = 0 := by
  rw [pList_eq, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨a, b⟩ := p
    exact within (mem_pairs' hp)
  · refine (nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    exact across (mem_pairs' hp) (mem_pairs' hq) hne

/- English proof (translation)
Introduce `X hX`. Rewrite `hX` using `[pList_eq, List.mem_flatMap]`. Take `⟨⟨a, b⟩, hp, hX⟩` from `hX`. Conclude with `norm_one (mem_pairs' hp) X hX`.
-/
theorem norm_pList (ε : Fin n → Bool) : ∀ X ∈ pList ε, B X X = 1 := by
  intro X hX
  rw [pList_eq, List.mem_flatMap] at hX
  obtain ⟨⟨a, b⟩, hp, hX⟩ := hX
  exact norm_one (mem_pairs' hp) X hX

end GlobalTheory.TypeSum.CasBasis.PB

namespace GlobalTheory.TypeSum.CasBasis

/- English proof (translation)
Introduce `n ε a b`. Establish `hpw` using `List.pairwise_iff_get.1 (PB.pairwise_pList ε)`. Use `show PB.B (pB ε a) (pB ε b) = _`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Rewrite using `[if_neg h.ne]`.

Conclude with `hpw a b h`. Rewrite using `[if_pos rfl]`. Conclude with `PB.norm_pList ε _ (List.get_mem _ _)`. Rewrite using `[if_neg h.ne', PB.B_comm]`. Conclude with `hpw b a h`.
-/
theorem pB_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length),
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  intro n ε a b
  have hpw := List.pairwise_iff_get.1 (PB.pairwise_pList ε)
  show PB.B (pB ε a) (pB ε b) = _
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg h.ne]; exact hpw a b h
  · rw [if_pos rfl]; exact PB.norm_pList ε _ (List.get_mem _ _)
  · rw [if_neg h.ne', PB.B_comm]; exact hpw b a h

end GlobalTheory.TypeSum.CasBasis

end
