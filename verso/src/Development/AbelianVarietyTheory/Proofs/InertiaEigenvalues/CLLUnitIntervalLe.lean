import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

/- English proof (translation)
Introduce `l h N v U U' hl hN hU hcard hb hv`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Unfold `LocalSituation.cLL LocalSituation.mN LocalSituation.rI LocalSituation.n0 at *`. Use `set L := Nat.log l (2 * h) with hL`. Use `set n0 := sInf {n | h + h ≤ l ^ n * (l - 1)} with hn0`.

Establish `hl1 : 1 < l` using `hl.one_lt`. Establish `hn0le : n0 ≤ L + 1`. Apply `Nat.sInf_le` to reduce the goal to its premises. Use `show h + h ≤ l ^ (L + 1) * (l - 1)`. Establish `h1 : 2 * h < l ^ (L + 1)` using `Nat.lt_pow_succ_log_self hl1 (2 * h)`.

Establish `h2 : l ^ (L + 1) ≤ l ^ (L + 1) * (l - 1)` using `Nat.le_mul_of_pos_right _ (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hI : Finset.Ico (0 : ℤ) 1 = {0}`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ico, Finset.mem_singleton]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hI, Finset.sum_singleton]`. Establish `hterm : ∀ u ∈ U, (∑ᶠ (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ 4 + 2 * L`. Introduce `u hu`. Establish `hz : LocalSituation.vZ l u ≤ Nat.log l h` using `vZ_le_log l h u (hb u hu)`.

Establish `hlog : Nat.log l h ≤ L` using `Nat.log_mono_right (by omega)`. Simplify using `only [finsum_eq_if, sub_zero]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hS : (∑ᶠ (u : ℤ) (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ N * (4 + 2 * L)`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := U) ?_]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_eq_mul]`. Conclude with `Nat.mul_le_mul_right _ hcard`. Introduce `u hu`. Rewrite `hu` using `[Function.mem_support]`.

Assume the negation of the conclusion as `hnot`. Establish `hnU' : u ∉ U'` using `fun h' => hnot (Finset.mem_coe.mpr (hU h'))`. Conclude with `hu (by simp only [finsum_eq_if, if_neg hnU'])`. Establish `hNL : 1 ≤ N * (4 + 2 * L)`. Use `Nat.mul_le_mul hN (show 1 ≤ 4 + 2 * L by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hmax` using `max_le hNL hS`. Use linear arithmetic over natural numbers and integers.
-/
theorem cLL_unit_interval_le : ∀ (l h N v : ℕ) (U : Finset ℤ) (U' : Set ℤ), l.Prime → 1 ≤ N → U' ⊆ U → U.card ≤ N →
    (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) → v ≤ LocalSituation.mN l 1 (h + h) - 1 →
    LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v U' 0 1 ≤ 5 + Nat.log l (2 * h) + N * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  intro l h N v U U' hl hN hU hcard hb hv
  haveI : Fact l.Prime := ⟨hl⟩
  unfold LocalSituation.cLL LocalSituation.mN LocalSituation.rI LocalSituation.n0 at *
  set L := Nat.log l (2 * h) with hL
  set n0 := sInf {n | h + h ≤ l ^ n * (l - 1)} with hn0
  have hl1 : 1 < l := hl.one_lt

  have hn0le : n0 ≤ L + 1 := by
    apply Nat.sInf_le
    show h + h ≤ l ^ (L + 1) * (l - 1)
    have h1 : 2 * h < l ^ (L + 1) := Nat.lt_pow_succ_log_self hl1 (2 * h)
    have h2 : l ^ (L + 1) ≤ l ^ (L + 1) * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton]

  have hterm : ∀ u ∈ U,
      (∑ᶠ (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ 4 + 2 * L := by
    intro u hu
    have hz : LocalSituation.vZ l u ≤ Nat.log l h := vZ_le_log l h u (hb u hu)
    have hlog : Nat.log l h ≤ L := Nat.log_mono_right (by omega)
    simp only [finsum_eq_if, sub_zero]
    split_ifs <;> omega

  have hS : (∑ᶠ (u : ℤ) (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0)))
      ≤ N * (4 + 2 * L) := by
    rw [finsum_eq_sum_of_support_subset _ (s := U) ?_]
    · calc _ ≤ U.card • (4 + 2 * L) := Finset.sum_le_card_nsmul _ _ _ hterm
        _ ≤ N * (4 + 2 * L) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
    · intro u hu
      rw [Function.mem_support] at hu
      by_contra hnot
      have hnU' : u ∉ U' := fun h' => hnot (Finset.mem_coe.mpr (hU h'))
      exact hu (by simp only [finsum_eq_if, if_neg hnU'])
  have hNL : 1 ≤ N * (4 + 2 * L) := by
    have := Nat.mul_le_mul hN (show 1 ≤ 4 + 2 * L by omega)
    omega
  have hmax := max_le hNL hS
  omega

end GlobalTheory.HubLoc
