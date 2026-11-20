import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isUp_one : IsUp g N 1 :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem isUp_mul {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) : IsUp g N (u * v) := by
  refine ⟨fun a => ?_, fun a c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hu.1, hv.1, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hu.2 a b h, zero_mul]
      · rw [hv.2 b a h, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with h' | h'
    · rw [hu.2 a b h', zero_mul]
    · rw [hv.2 b c (lt_of_lt_of_le h h'), mul_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mul_entry {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) {a c : Fin N} (hac : a < c)
    (h : ∀ b, a < b → b < c → u.val a b * v.val b c = 0) : (u * v).val a c = u.val a c + v.val a c := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac.ne]
  · rw [hu.1, hv.1, one_mul, mul_one, add_comm]
  · rintro b _ ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · rw [hu.2 a b h1, zero_mul]
    rcases lt_or_gt_of_ne h2 with h2 | h2
    · exact h b h1 h2
    · rw [hv.2 b c h2, mul_zero]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isNilpotent_of_isUp {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [Matrix.sub_apply, hu.2 a b h', Matrix.one_apply_ne h'.ne']
  have hc := Matrix.aeval_self_charpoly (u.val - 1)
  rw [Matrix.charpoly_of_upperTriangular _ ht] at hc
  refine ⟨N, ?_⟩
  simpa [Matrix.sub_apply, hu.1] using hc

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem edge_lt (L : Lev g N) {a b : Fin N} (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩
  have : a ≠ b := fun h => by subst h; omega
  simp [Matrix.one_apply_ne this]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem mem_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.Mem (u * v) := by
  refine ⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩
  rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]
  intro b hb hc
  rw [Fin.lt_def] at hb hc
  rw [hv.2 hs b c (by omega) (by omega) h3, mul_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem edge_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) {a c : Fin N} (h : L.Edge a c) :
    (u * v).val a c = u.val a c + v.val a c := by
  refine mul_entry hu.1 hv.1 (edge_lt L h) fun b hb hc => ?_
  rw [Fin.lt_def] at hb hc
  unfold Lev.Edge at h
  split_ifs at h with hs
  · rcases h with h | h
    · omega
    · rw [hv.2 hs b c (by omega) (by omega) h.2, mul_zero]
  · omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  unfold Lev.chi
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
  refine fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · simp [Matrix.one_apply_ne (edge_lt L h).ne]
  · rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem chi_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.chi (u * v) = L.chi u * L.chi v := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [edge_mul L hu hv h, mul_add]
  · simp

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
