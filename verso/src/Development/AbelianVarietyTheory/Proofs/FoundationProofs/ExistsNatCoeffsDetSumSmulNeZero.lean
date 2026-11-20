import Mathlib
open scoped Matrix
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_affine_eval {K : Type} [Field K] {m : ℕ} (U V : Matrix (Fin m) (Fin m) K) (t : K) :
    ((X : K[X]) • V.map C + U.map C).det.eval t = (U + t • V).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_nat_det_ne_zero_affine {K : Type} [Field K] [CharZero K] {m : ℕ}
    (U V : Matrix (Fin m) (Fin m) K) (t : K) (h : (U + t • V).det ≠ 0) :
    ∃ k : ℕ, (U + (k : K) • V).det ≠ 0 := by
  classical
  set p : K[X] := ((X : K[X]) • V.map C + U.map C).det
  have hp : p ≠ 0 := by
    intro h0
    apply h
    rw [← det_affine_eval]
    simp [p, h0]
  by_contra hall
  push_neg at hall
  have hsub : Set.range (fun k : ℕ => (k : K)) ⊆ (p.roots.toFinset : Set K) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot, det_affine_eval]
    exact hall k
  have hinf : (Set.range (fun k : ℕ => (k : K))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  exact hinf ((p.roots.toFinset.finite_toSet).subset hsub)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_nat_coeffs_on_finset_det_sum_ne_zero {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (s : Finset (Fin n)) :
    ∀ b : Fin n → K, (∑ i, b i • T i).det ≠ 0 →
      ∃ b' : Fin n → K, (∑ i, b' i • T i).det ≠ 0 ∧ ∀ i ∈ s, ∃ k : ℕ, b' i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro b hb; exact ⟨b, hb, by simp⟩
  | insert j s hj ih =>
    intro b hb
    obtain ⟨b₁, hb₁, hs⟩ := ih b hb
    have key : ∀ t : K, ∑ i, Function.update b₁ j t i • T i
        = (∑ i, Function.update b₁ j 0 i • T i) + t • T j := by
      intro t
      have h1 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j t i • T i) (Finset.mem_univ j)
      have h2 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j 0 i • T i) (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update b₁ j t i • T i
          = ∑ i ∈ Finset.univ.erase j, Function.update b₁ j 0 i • T i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← h1, ← h2, h3]
      simp
    have hb₁' : ((∑ i, Function.update b₁ j 0 i • T i) + b₁ j • T j).det ≠ 0 := by
      rw [← key, Function.update_eq_self]; exact hb₁
    obtain ⟨k, hk⟩ := exists_nat_det_ne_zero_affine _ _ _ hb₁'
    refine ⟨Function.update b₁ j (k : K), by rw [key]; exact hk, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := hs i hi'
      refine ⟨k', ?_⟩
      rw [Function.update_of_ne (by rintro rfl; exact hj hi')]
      exact hk'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_nat_coeffs_det_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K),
    (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  intro K _ _ m n T b hb
  obtain ⟨b', hb', hs⟩ := exists_nat_coeffs_on_finset_det_sum_ne_zero T Finset.univ b hb
  choose a ha using fun i => hs i (Finset.mem_univ i)
  refine ⟨a, ?_⟩
  simp_rw [← ha]; exact hb'

end GlobalTheory
