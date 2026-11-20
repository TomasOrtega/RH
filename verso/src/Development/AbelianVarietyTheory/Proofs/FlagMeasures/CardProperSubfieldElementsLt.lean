import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.SubfieldCount

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1 : 0 < g ^ (m + 1)` using `pow_pos (by omega) _`.

Establish `h2 : 5 * g ^ m ≤ g ^ (m + 1)`. Rewrite using `[pow_succ, mul_comm]`. Conclude with `Nat.mul_le_mul_left _ hg`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_bound {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    4 * (∑ e ∈ Finset.range m, (g ^ (e + 1) - 1)) + 4 * m + 5 ≤ 5 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < g ^ (m + 1) := pow_pos (by omega) _
    have h2 : 5 * g ^ m ≤ g ^ (m + 1) := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hg
    omega

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hg`. Consider the case `succ m ih`. Establish `h2 : g ^ (m + 1) * 5 ≤ g ^ (m + 1 + 1)`. Rewrite using `[pow_succ g (m + 1)]`.

Conclude with `Nat.mul_le_mul_left _ hg`. Use linear arithmetic over natural numbers and integers.
-/
theorem five_mul_le {g : ℕ} (hg : 5 ≤ g) (m : ℕ) : 5 * (m + 1) ≤ g ^ (m + 1) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    have h2 : g ^ (m + 1) * 5 ≤ g ^ (m + 1 + 1) := by
      rw [pow_succ g (m + 1)]; exact Nat.mul_le_mul_left _ hg
    omega

/- English proof (translation)
Establish `key : ∀ m : ℕ, 4 * (m + 1) * (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) + 1 < g ^ (2 * (m + 1))`. Introduce `m`. Establish `h1` using `sum_bound hg (m + 1)`. Establish `h2` using `five_mul_le hg m`. Rewrite using `[two_mul (m + 1), pow_add]`.

Generalize the expression as in `(∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *`. Generalize the expression as in `g ^ (m + 1) = x at *`. Establish `h3` using `Nat.mul_le_mul_left (m + 1) h1`. Establish `h4` using `Nat.mul_le_mul_right x h2`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨m, rfl | rfl⟩` from `Nat.even_or_odd' d`. Take `⟨m, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `h` using `key m`. Rewrite using `[show 2 * (m + 1) / 2 = m + 1 by omega, show 2 * (2 * (m + 1)) = 4 * (m + 1) by ring]`. Use linear arithmetic over natural numbers and integers.

Break down `m with _ | m` into its components or cases. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `h` using `key m`. Rewrite using `[show (2 * (m + 1) + 1) / 2 = m + 1 by omega, pow_succ g (2 * (m + 1))]`.

Generalize the expression as in `(∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *`. Generalize the expression as in `g ^ (2 * (m + 1)) = x at *`. Establish `h4` using `Nat.mul_le_mul_left x hg`. Apply `Nat.lt_sub_of_add_lt` to reduce the goal to its premises. Use polynomial arithmetic with `[Nat.zero_le (m * T), Nat.zero_le T]`.
-/
theorem num_bound {g : ℕ} (hg : 5 ≤ g) {d : ℕ} (hd : 0 < d) :
    2 * d * (∑ e ∈ Finset.range (d / 2), (g ^ (e + 1) - 1)) < g ^ d - 1 := by
  have key : ∀ m : ℕ, 4 * (m + 1) * (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) + 1
      < g ^ (2 * (m + 1)) := by
    intro m
    have h1 := sum_bound hg (m + 1)
    have h2 := five_mul_le hg m
    rw [two_mul (m + 1), pow_add]
    generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
    generalize g ^ (m + 1) = x at *
    have h3 := Nat.mul_le_mul_left (m + 1) h1
    have h4 := Nat.mul_le_mul_right x h2
    nlinarith
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h := key m
    rw [show 2 * (m + 1) / 2 = m + 1 by omega, show 2 * (2 * (m + 1)) = 4 * (m + 1) by ring]
    omega
  · rcases m with _ | m
    · simp; omega
    · have h := key m
      rw [show (2 * (m + 1) + 1) / 2 = m + 1 by omega, pow_succ g (2 * (m + 1))]
      generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
      generalize g ^ (2 * (m + 1)) = x at *
      have h4 := Nat.mul_le_mul_left x hg
      apply Nat.lt_sub_of_add_lt
      nlinarith [Nat.zero_le (m * T), Nat.zero_le T]

/- English proof (translation)
Establish `hx : IsIntegral (ZMod g) z` using `Algebra.IsIntegral.isIntegral z`. Rewrite using `[(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff, Nat.card_zmod]`. Simplify using `[sub_eq_zero]`.
-/
theorem natDegree_dvd_iff {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (n : ℕ) :
    (minpoly (ZMod g) z).natDegree ∣ n ↔ z ^ (g ^ n) = z := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff,
    Nat.card_zmod]
  simp [sub_eq_zero]

end GlobalTheory.GLm.SubfieldCount

namespace GlobalTheory.GLm
open SubfieldCount

/- English proof (translation)
Introduce `g _ d hg hd`. Use `lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) (num_bound hg hd)` and prove the remaining obligations. Set `F : Finset (Formalism.CyclotomicNorms.Fbar g)` to `(Finset.range (d / 2)).biUnion fun e => (nthRoots (g ^ (e + 1) - 1) (1 : Formalism.CyclotomicNorms.Fbar g)).toFinset`. Establish `hsub : {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧ (minpoly (ZMod g) z).natDegree ≠ d} ⊆ (F : Set _)`. Introduce and unpack `z ⟨h0, hz, hne⟩`.

Establish `hx : IsIntegral (ZMod g) z` using `Algebra.IsIntegral.isIntegral z`. Establish `hpos` using `minpoly.natDegree_pos hx`. Establish `h1` using `(natDegree_dvd_iff z _).1 dvd_rfl`. Take `⟨k, hk⟩` from `(natDegree_dvd_iff z d).2 hz`. Take `⟨e, he⟩ : ∃ e, (minpoly (ZMod g) z).natDegree = e + 1` from `⟨(minpoly (ZMod g) z).natDegree - 1, by omega⟩`.

Rewrite `hk`, `h1`, `hne` using `[he]`. Establish `hk2 : 2 ≤ k`. Break down `k with _ | _ | k` into its components or cases. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hle : (e + 1) * 2 ≤ d` using `hk ▸ Nat.mul_le_mul_left _ hk2`. Establish `hp : 1 < g ^ (e + 1)` using `Nat.one_lt_pow (by omega) (by omega)`. Simplify using `only [F, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.mem_coe, Multiset.mem_toFinset]`. Use `⟨e, by simp only [Set.mem_Iio]; omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_nthRoots (by omega)]`. Apply `mul_right_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[← pow_succ, one_mul, Nat.sub_add_cancel hp.le, h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_proper_subfield_elements_lt : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 5 ≤ g → 0 < d →
    2 * d * Nat.card {z : Formalism.CyclotomicNorms.Fbar g // z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} < g ^ d - 1 := by
  intro g _ d hg hd
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) (num_bound hg hd)
  let F : Finset (Formalism.CyclotomicNorms.Fbar g) := (Finset.range (d / 2)).biUnion fun e =>
    (nthRoots (g ^ (e + 1) - 1) (1 : Formalism.CyclotomicNorms.Fbar g)).toFinset
  have hsub : {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} ⊆ (F : Set _) := by
    rintro z ⟨h0, hz, hne⟩
    have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
    have hpos := minpoly.natDegree_pos hx
    have h1 := (natDegree_dvd_iff z _).1 dvd_rfl
    obtain ⟨k, hk⟩ := (natDegree_dvd_iff z d).2 hz
    obtain ⟨e, he⟩ : ∃ e, (minpoly (ZMod g) z).natDegree = e + 1 :=
      ⟨(minpoly (ZMod g) z).natDegree - 1, by omega⟩
    rw [he] at hk h1 hne
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have hle : (e + 1) * 2 ≤ d := hk ▸ Nat.mul_le_mul_left _ hk2
    have hp : 1 < g ^ (e + 1) := Nat.one_lt_pow (by omega) (by omega)
    simp only [F, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset]
    refine ⟨e, by simp only [Set.mem_Iio]; omega, ?_⟩
    rw [mem_nthRoots (by omega)]
    apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel hp.le, h1]
  calc _ = Set.ncard {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} := rfl
    _ ≤ (F : Set _).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ _ := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ =>
        (Multiset.toFinset_card_le _).trans (card_nthRoots _ _))

end GlobalTheory.GLm
