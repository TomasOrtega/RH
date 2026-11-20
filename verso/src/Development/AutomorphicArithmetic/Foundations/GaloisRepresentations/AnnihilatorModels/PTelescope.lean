import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Use `⟨fun _ => ?_, fun h => absurd ⟨0, rfl⟩ h⟩` and prove the remaining obligations. Simplify using `[h0]`. Consider the case `succ m ih`.

Establish `hmn : m < n` using `hm`. Take `⟨ihE, ihO⟩` from `ih (by omega)`. Establish `key : (T (m + 1)).map F^[n - (m + 1)] = (A m).map F^[n - m] + q ^ (m + 1) • (A (m + 1)).map F^[n - (m + 1)]`. Rewrite using `[hs m hmn, Multiset.map_add, Multiset.map_nsmul, Multiset.map_map]`. Use `congr 2`.

Establish `e : n - m = (n - (m + 1)) + 1` using `by omega`. Rewrite using `[e, Function.iterate_succ]`. Establish `hc : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1)`. Rewrite using `[Nat.choose_succ_succ', Nat.choose_one_right, add_comm]`. Simplify using `only [Finset.sum_range_succ _ (m + 1), key, hc, pow_add, smul_add, mul_smul]`.

Break down `Nat.even_or_odd m with he | ho` into its components or cases. Establish `hne : ¬ Even (m + 1)` using `Nat.not_even_iff_odd.mpr he.add_one`. Simplify using `only [hne, if_false, zero_smul, add_zero, if_true]`. Use `⟨fun h => h.elim, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[ihE he]`.

Normalize the expressions using the abelian group laws. Establish `hne : ¬ Even m` using `Nat.not_even_iff_odd.mpr ho`. Establish `hev : Even (m + 1)` using `ho.add_one`. Simplify using `only [hev, if_false, zero_smul, add_zero, if_true]`. Use `⟨fun _ => ?_, fun h => absurd trivial h⟩` and prove the remaining obligations.

Rewrite using `[ihO hne]`. Normalize the expressions using the abelian group laws.
-/
private theorem telescope_core {P : Type} (q n : ℕ) (F : P → P) (T A : ℕ → Multiset P)
    (h0 : T 0 = A 0)
    (hs : ∀ j, j < n → T (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1)) (m : ℕ) (hm : m ≤ n) :
    (Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) ∧
    (¬ Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd ⟨0, rfl⟩ h⟩
    simp [h0]
  | succ m ih =>
    have hmn : m < n := hm
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    have key : (T (m + 1)).map F^[n - (m + 1)] =
        (A m).map F^[n - m] + q ^ (m + 1) • (A (m + 1)).map F^[n - (m + 1)] := by
      rw [hs m hmn, Multiset.map_add, Multiset.map_nsmul, Multiset.map_map]
      congr 2
      have e : n - m = (n - (m + 1)) + 1 := by omega
      rw [e, Function.iterate_succ]
    have hc : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    simp only [Finset.sum_range_succ _ (m + 1), key, hc, pow_add, smul_add, mul_smul]
    rcases Nat.even_or_odd m with he | ho
    · have hne : ¬ Even (m + 1) := Nat.not_even_iff_odd.mpr he.add_one
      simp only [hne, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun h => h.elim, fun _ => ?_⟩
      rw [ihE he]
      abel
    · have hne : ¬ Even m := Nat.not_even_iff_odd.mpr ho
      have hev : Even (m + 1) := ho.add_one
      simp only [hev, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
      rw [ihO hne]
      abel

/- English proof (translation)
Introduce `q n P F T A hAn h0 hs`. Set `T' : ℕ → Multiset P` to `fun j => if h : j < n + 1 then T ⟨j, h⟩ else 0`. Establish `hT : ∀ j : Fin (n + 1), T j = T' j` using `fun j => by`. Simplify using `only [T', dif_pos j.isLt, Fin.eta]`. Establish `h0' : T' 0 = A 0` using `by simpa [T'] using h0`.

Establish `hs' : ∀ j, j < n → T' (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1)`. Introduce `j hj`. Establish `hh` using `hs ⟨j, hj⟩`. Simplify `hh` using `[T', hj, Fin.succ]`. Establish `hE : ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] = ∑ j ∈ Finset.range (n + 1), (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j]`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun j => (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j])]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hT j]`. Both sides reduce to the same expression. Establish `hO : ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j] = ∑ j ∈ Finset.range (n + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j]`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun j => (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j])]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hT j]`. Both sides reduce to the same expression. Take `⟨h1, h2⟩` from `telescope_core q n F T' A h0' hs' n le_rfl`.

Rewrite using `[hE, hO]`. Distinguish the cases in `he : Even n`. Rewrite using `[h1 he]`. Simplify using `[hAn]`. Rewrite using `[h2 he]`.

Simplify using `[hAn]`.
-/
theorem UpperTheory.Gal.crystallineComparison.telescope_of :
    Telescope := by
  intro q n P F T A hAn h0 hs
  let T' : ℕ → Multiset P := fun j => if h : j < n + 1 then T ⟨j, h⟩ else 0
  have hT : ∀ j : Fin (n + 1), T j = T' j := fun j => by
    simp only [T', dif_pos j.isLt, Fin.eta]
  have h0' : T' 0 = A 0 := by simpa [T'] using h0
  have hs' : ∀ j, j < n → T' (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1) := by
    intro j hj
    have hh := hs ⟨j, hj⟩
    simpa [T', hj, Fin.succ] using hh
  have hE : ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  have hO : ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  obtain ⟨h1, h2⟩ := telescope_core q n F T' A h0' hs' n le_rfl
  rw [hE, hO]
  by_cases he : Even n
  · rw [h1 he]
    simp [hAn]
  · rw [h2 he]
    simp [hAn]
