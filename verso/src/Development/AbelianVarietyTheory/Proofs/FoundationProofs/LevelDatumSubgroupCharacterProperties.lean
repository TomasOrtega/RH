import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩`.
-/
theorem isUp_one : IsUp g N 1 :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

/- English proof (translation)
Use `⟨fun a => ?_, fun a c h => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[hu.1, hv.1, mul_one]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases.

Rewrite using `[hu.2 a b h, zero_mul]`. Rewrite using `[hv.2 b a h, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge b a with h' | h'` into its components or cases. Rewrite using `[hu.2 a b h', zero_mul]`. Rewrite using `[hv.2 b c (lt_of_lt_of_le h h'), mul_zero]`.
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
Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac.ne]`. Rewrite using `[hu.1, hv.1, one_mul, mul_one, add_comm]`. Introduce and unpack `b _ ⟨h1, h2⟩`. Break down `lt_or_gt_of_ne h1 with h1 | h1` into its components or cases. Rewrite using `[hu.2 a b h1, zero_mul]`.

Break down `lt_or_gt_of_ne h2 with h2 | h2` into its components or cases. Conclude with `h b h1 h2`. Rewrite using `[hv.2 b c h2, mul_zero]`.
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
Establish `ht : (u.val - 1).BlockTriangular id`. Introduce `a b h`. Establish `h' : b < a` using `h`. Simplify using `[Matrix.sub_apply, hu.2 a b h', Matrix.one_apply_ne h'.ne']`. Establish `hc` using `Matrix.aeval_self_charpoly (u.val - 1)`.

Rewrite `hc` using `[Matrix.charpoly_of_upperTriangular _ ht]`. Use `⟨N, ?_⟩` and prove the remaining obligations. Simplify `hc` using `[Matrix.sub_apply, hu.1]`.
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
Unfold `Lev.Edge at h`. Rewrite using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
theorem edge_lt (L : Lev g N) {a b : Fin N} (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

/- English proof (translation)
Use `⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩` and prove the remaining obligations. Establish `: a ≠ b` using `fun h => by subst h; omega`. Simplify using `[Matrix.one_apply_ne this]`.
-/
theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩
  have : a ≠ b := fun h => by subst h; omega
  simp [Matrix.one_apply_ne this]

/- English proof (translation)
Use `⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]`. Introduce `b hb hc`. Rewrite `hb`, `hc` using `[Fin.lt_def]`. Rewrite using `[hv.2 hs b c (by omega) (by omega) h3, mul_zero]`.
-/
theorem mem_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.Mem (u * v) := by
  refine ⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩
  rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]
  intro b hb hc
  rw [Fin.lt_def] at hb hc
  rw [hv.2 hs b c (by omega) (by omega) h3, mul_zero]

/- English proof (translation)
Apply the tactic sequence `refine mul_entry hu.1 hv.1 (edge_lt L h) fun b hb hc => ?_`. Rewrite `hb`, `hc` using `[Fin.lt_def]`. Unfold `Lev.Edge at h`. Use `split_ifs at h with hs`. Break down `h with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hv.2 hs b c (by omega) (by omega) h.2, mul_zero]`. Use linear arithmetic over natural numbers and integers.
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
Unfold `Lev.chi`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one]`. Use `fun a _ => Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[Matrix.one_apply_ne (edge_lt L h).ne]`.

Both sides reduce to the same expression.
-/
theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  unfold Lev.chi
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
  refine fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · simp [Matrix.one_apply_ne (edge_lt L h).ne]
  · rfl

/- English proof (translation)
Unfold `Lev.chi`. Rewrite using `[← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[edge_mul L hu hv h, mul_add]`. Simplify using the standard rewrite rules.
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
Introduce `_ _ _ L` and use `⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩`.
-/
theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
