import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet

/- English proof (translation)
Rewrite using `[List.count_cons]`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[add_comm]`. Establish `h' : ¬ a = i` using `fun e => h e.symm`.

Simplify using `[h, h', Pi.single_apply]`.
-/
theorem count_cons_eq_single_add {I : Type} [DecidableEq I] (a : I) (l : List I) (i : I) :
    (a :: l).count i = (Pi.single a 1 : I → ℕ) i + l.count i := by
  rw [List.count_cons]
  by_cases h : i = a
  · subst h; simp [add_comm]
  · have h' : ¬ a = i := fun e => h e.symm
    simp [h, h', Pi.single_apply]

/- English proof (translation)
Introduce `R _ I _ n J l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `hc`. Establish `: (⟨fun i => List.count i ([] : List I), hc⟩ : Idx I n) = ⟨0, by simp⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this, J.one]`. Simplify using the standard rewrite rules.

Consider the case `cons a l ih`. Introduce `hc`. Establish `hc' : ∑ i, l.count i ≤ n + 1` using `le_trans (Finset.sum_le_sum fun i _ => List.count_le_count_cons ..) hc`. Establish `hsum : ∑ i, ((Pi.single a 1 : I → ℕ) + fun i => l.count i) i ≤ n + 1`. Use `le_of_eq_of_le ?_ hc` and prove the remaining obligations.

Conclude with `Finset.sum_congr rfl fun i _ => (count_cons_eq_single_add a l i).symm`. Rewrite using `[List.map_cons, List.prod_cons, ih hc', mul_smul_comm, JetRing.t, J.mul, dif_pos hsum, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← Nat.cast_mul]`. Establish `hidx : (⟨(Pi.single a 1 : I → ℕ) + fun i => l.count i, hsum⟩ : Idx I n) = ⟨fun i => (a :: l).count i, hc⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Conclude with `(count_cons_eq_single_add a l i).symm`. Establish `hprod : (∏ i, ((a :: l).count i).factorial) = (∏ i, ((Pi.single a 1 : I → ℕ) i + l.count i).choose ((Pi.single a 1 : I → ℕ) i)) * ∏ i, (l.count i).factorial`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[count_cons_eq_single_add]`.

Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[Nat.factorial_succ, add_comm]`. Simplify using `[Pi.single_apply, h]`. Rewrite using `[hidx, hprod, mul_comm]`.
-/
theorem prod_map_t_eq_smul_b : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1),
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  intro R _ I _ n J l
  induction l with
  | nil =>
    intro hc
    have : (⟨fun i => List.count i ([] : List I), hc⟩ : Idx I n) = ⟨0, by simp⟩ := by
      apply Subtype.ext; funext i; simp
    rw [this, J.one]; simp
  | cons a l ih =>
    intro hc
    have hc' : ∑ i, l.count i ≤ n + 1 :=
      le_trans (Finset.sum_le_sum fun i _ => List.count_le_count_cons ..) hc
    have hsum : ∑ i, ((Pi.single a 1 : I → ℕ) + fun i => l.count i) i ≤ n + 1 := by
      refine le_of_eq_of_le ?_ hc
      exact Finset.sum_congr rfl fun i _ => (count_cons_eq_single_add a l i).symm
    rw [List.map_cons, List.prod_cons, ih hc', mul_smul_comm, JetRing.t, J.mul, dif_pos hsum,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, ← Nat.cast_mul]
    have hidx : (⟨(Pi.single a 1 : I → ℕ) + fun i => l.count i, hsum⟩ : Idx I n) = ⟨fun i => (a :: l).count i, hc⟩ := by
      apply Subtype.ext; funext i; exact (count_cons_eq_single_add a l i).symm
    have hprod : (∏ i, ((a :: l).count i).factorial) =
        (∏ i, ((Pi.single a 1 : I → ℕ) i + l.count i).choose ((Pi.single a 1 : I → ℕ) i)) * ∏ i, (l.count i).factorial := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [count_cons_eq_single_add]
      by_cases h : i = a
      · subst h; simp [Nat.factorial_succ, add_comm]
      · simp [Pi.single_apply, h]
    rw [hidx, hprod, mul_comm]

end GlobalTheory.LatJet
