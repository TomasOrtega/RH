import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe

namespace GlobalTheory

open Matrix

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `(IsLocalRing.mem_maximalIdeal _).mp _ h` to reduce the goal to its premises. Conclude with `Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)`.
-/
theorem exists_isUnit_of_isUnit_sum_localRing {R : Type} [CommRing R] [IsLocalRing R]
    {ι : Type} (s : Finset ι) (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  apply (IsLocalRing.mem_maximalIdeal _).mp _ h
  exact Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)

/- English proof (translation)
Introduce `R _ _ m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `M _`. Use `⟨1, fun k hk => ?_⟩` and prove the remaining obligations.

Take `rfl : k = 0` from `Nat.le_zero.mp hk`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `M hM`. Rewrite `hM` using `[Matrix.det_succ_row M (Fin.last n)]`.

Take `⟨j, -, hj⟩` from `exists_isUnit_of_isUnit_sum_localRing _ _ hM`. Establish `hN` using `isUnit_of_mul_isUnit_right hj`. Rewrite `hN` using `[Fin.succAbove_last]`. Take `⟨v, hv⟩` from `ih _ hN`. Set `f : Fin (n + 1) → Fin (n + 1)` to `fun i => if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))`.

Establish `hf : Function.Injective f`. Introduce `a b hab`. Simplify using `only [f] at hab`. Apply the tactic sequence `by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n`. Rewrite using `[ha, hb]`.

Simplify using `only [ha, hb, dite_true, dite_false] at hab`. Conclude with `absurd hab.symm (Fin.succAbove_ne _ _)`. Simplify using `only [ha, hb, dite_true, dite_false] at hab`. Conclude with `absurd hab (Fin.succAbove_ne _ _)`. Simplify using `only [ha, hb, dite_false] at hab`.

Use `v.injective (Fin.succAbove_right_injective hab)` as an intermediate fact. Conclude with `Fin.castPred_inj.mp this`. Set `w : Equiv.Perm (Fin (n + 1))` to `Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)`. Use `⟨w, fun k hk => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge k (n + 1) with hlt | hge` into its components or cases.

Establish `hk' : k ≤ n` using `Nat.lt_succ_iff.mp hlt`. Establish `heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) = ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix (Fin.castLE hk') (Fin.castLE hk')`. Use extensionality with `a b`. Establish `hb : Fin.castLE hk b ≠ Fin.last n`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]`. Use `congr 2`.

Apply the tactic sequence `all_goals (ext; simp)`. Rewrite using `[heq]`. Conclude with `hv k hk'`. Take `rfl : k = n + 1` from `le_antisymm hk hge`. Establish `: Fin.castLE hk = id` using `Fin.castLE_rfl _`.

Rewrite using `[this, Matrix.submatrix_id_id, Matrix.det_permute']`. Use `IsUnit.mul ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]`. Rewrite using `[Matrix.det_succ_row M (Fin.last n)]`. Conclude with `hM`.
-/
theorem exists_perm_isUnit_leading_minors_localRing :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R),
      IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m),
        IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  intro R _ _ m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ n ih =>
    intro M hM
    rw [Matrix.det_succ_row M (Fin.last n)] at hM
    obtain ⟨j, -, hj⟩ := exists_isUnit_of_isUnit_sum_localRing _ _ hM
    have hN := isUnit_of_mul_isUnit_right hj
    rw [Fin.succAbove_last] at hN
    obtain ⟨v, hv⟩ := ih _ hN
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n
      · rw [ha, hb]
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab.symm (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_false] at hab
        have := v.injective (Fin.succAbove_right_injective hab)
        exact Fin.castPred_inj.mp this
    let w : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix
            (Fin.castLE hk') (Fin.castLE hk') := by
        ext a b
        have hb : Fin.castLE hk b ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]
        congr 2
        all_goals (ext; simp)
      rw [heq]
      exact hv k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      have : Fin.castLE hk = id := Fin.castLE_rfl _
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute']
      refine IsUnit.mul ?_ ?_
      · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
      · rw [Matrix.det_succ_row M (Fin.last n)]
        exact hM

end GlobalTheory
