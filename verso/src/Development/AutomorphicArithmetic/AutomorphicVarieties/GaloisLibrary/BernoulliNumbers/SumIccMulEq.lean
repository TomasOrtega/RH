import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BRaabe

open Finset UpperTheory.V.Bern

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]`.
-/
private theorem sum_Icc_one_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/- English proof (translation)
Repeatedly rewrite using `[sum_Icc_one_eq]`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_Icc_mul_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (N m : ℕ) :
    ∑ x ∈ Icc 1 (N * m), f x = ∑ j ∈ range m, ∑ a ∈ Icc 1 N, f (a + j * N) := by
  simp_rw [sum_Icc_one_eq]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

/- English proof (translation)
Introduce `R _ _ N M h k Φ hM`. Take `⟨m, rfl⟩` from `h`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hM)`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hM)`. Unfold `genB`.

Rewrite using `[sum_Icc_mul_eq]`. Repeatedly rewrite using `[b_raabe N m k _ hN hm, map_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 2`.

Rewrite using `[map_natCast]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Bern.b_comp :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N M : ℕ} (h : N ∣ M) (k : ℕ) (Φ : ZMod N → R), 0 < M → genB k (fun a : ZMod M => Φ (ZMod.castHom h (ZMod N) a)) = genB k Φ := by
  intro R _ _ N M h k Φ hM
  obtain ⟨m, rfl⟩ := h
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  unfold genB
  rw [sum_Icc_mul_eq]
  simp_rw [b_raabe N m k _ hN hm, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [map_natCast]
  simp
