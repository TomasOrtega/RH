import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `T hT`. Use `⟨id, Function.injective_id, fun k hk => ?_⟩` and prove the remaining obligations.

Take `rfl : k = 0` from `Nat.le_zero.mp hk`. Establish `h1 : T.det = 1` using `Matrix.det_isEmpty`. Rewrite using `[Matrix.det_isEmpty]`. Rewrite `hT` using `[h1]`. Then use the resulting hypothesis. Consider the case `succ n ih`.

Introduce `T hT`. Establish `hsum` using `T.det_succ_column (Fin.last n)`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i : Fin (n+1), (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * T i (Fin.last n) * (T.submatrix i.succAbove (Fin.last n).succAbove).det ∉ p := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hT (hsum ▸ p.sum_mem fun i _ => h i)`. Establish `hM : (T.submatrix i.succAbove Fin.castSucc).det ∉ p`. Introduce `hm`. Apply `hi` to reduce the goal to its premises. Rewrite using `[Fin.succAbove_last]`.

Conclude with `p.mul_mem_left _ hm`. Take `⟨g, hg, hmin⟩` from `ih _ hM`. Use `set f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (g j))`. Establish `hf : Function.Injective f`. Introduce `a b hab`.

Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rfl`. Consider the case `cast b`.

Simplify using `only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab`. Conclude with `absurd hab.symm (Fin.succAbove_ne i _)`. Consider the case `cast a`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab`. Conclude with `absurd hab (Fin.succAbove_ne i _)`. Consider the case `cast b`. Simplify using `only [f, Fin.lastCases_castSucc] at hab`. Rewrite using `[hg (Fin.succAbove_right_injective hab)]`.

Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Break down `Nat.lt_or_ge k (n+1) with hlt | hge` into its components or cases. Establish `hk' : k ≤ n` using `Nat.lt_succ_iff.mp hlt`. Establish `hmat : (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) = Matrix.of fun a b : Fin k => (T.submatrix i.succAbove Fin.castSucc) (g (Fin.castLE hk' a)) (Fin.castLE hk' b)`.

Use extensionality with `a b`. Establish `e1 : (Fin.castLE hk a : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' a)` using `Fin.ext rfl`. Establish `e2 : (Fin.castLE hk b : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' b)` using `Fin.ext rfl`. Rewrite using `[Matrix.of_apply, Matrix.of_apply, e1, e2]`. Simplify using `only [f, Fin.lastCases_castSucc, Matrix.submatrix_apply]`.

Rewrite using `[hmat]`. Conclude with `hmin k hk'`. Take `rfl : k = n + 1` from `le_antisymm hk hge`. Set `σ : Equiv.Perm (Fin (n+1))` to `Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)`. Establish `hmat : (Matrix.of fun a b : Fin (n+1) => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) = T.submatrix σ id`.

Use extensionality with `a b`. Establish `e1 : Fin.castLE hk a = a` using `Fin.ext rfl`. Establish `e2 : Fin.castLE hk b = b` using `Fin.ext rfl`. Simplify using `[σ, e1, e2]`. Rewrite using `[hmat, Matrix.det_permute]`.

Introduce `hm`. Apply `hT` to reduce the goal to its premises. Establish `hs : T.det = ((Equiv.Perm.sign σ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R) * T.det)`. Rewrite using `[← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules.

Rewrite using `[hs]`. Conclude with `p.mul_mem_left _ hm`.
-/
theorem exists_injective_rows_leadingMinors_not_mem (R : Type) [CommRing R] (p : Ideal R) :
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) R), T.det ∉ p →
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ (k : ℕ) (hk : k ≤ n),
      (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)).det ∉ p := by
  intro n
  induction n with
  | zero =>
    intro T hT
    refine ⟨id, Function.injective_id, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    have h1 : T.det = 1 := Matrix.det_isEmpty
    rw [Matrix.det_isEmpty]
    rwa [h1] at hT
  | succ n ih =>
    intro T hT
    have hsum := T.det_succ_column (Fin.last n)
    obtain ⟨i, hi⟩ : ∃ i : Fin (n+1), (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * T i (Fin.last n) *
        (T.submatrix i.succAbove (Fin.last n).succAbove).det ∉ p := by
      by_contra h
      push_neg at h
      exact hT (hsum ▸ p.sum_mem fun i _ => h i)
    have hM : (T.submatrix i.succAbove Fin.castSucc).det ∉ p := by
      intro hm
      apply hi
      rw [Fin.succAbove_last]
      exact p.mul_mem_left _ hm
    obtain ⟨g, hg, hmin⟩ := ih _ hM
    set f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (g j))
    have hf : Function.Injective f := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab.symm (Fin.succAbove_ne i _)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab (Fin.succAbove_ne i _)
        | cast b =>
          simp only [f, Fin.lastCases_castSucc] at hab
          rw [hg (Fin.succAbove_right_injective hab)]
    refine ⟨f, hf, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have hmat : (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          Matrix.of fun a b : Fin k => (T.submatrix i.succAbove Fin.castSucc)
            (g (Fin.castLE hk' a)) (Fin.castLE hk' b) := by
        ext a b
        have e1 : (Fin.castLE hk a : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' a) := Fin.ext rfl
        have e2 : (Fin.castLE hk b : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' b) := Fin.ext rfl
        rw [Matrix.of_apply, Matrix.of_apply, e1, e2]
        simp only [f, Fin.lastCases_castSucc, Matrix.submatrix_apply]
      rw [hmat]
      exact hmin k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
      have hmat : (Matrix.of fun a b : Fin (n+1) => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          T.submatrix σ id := by
        ext a b
        have e1 : Fin.castLE hk a = a := Fin.ext rfl
        have e2 : Fin.castLE hk b = b := Fin.ext rfl
        simp [σ, e1, e2]
      rw [hmat, Matrix.det_permute]
      intro hm
      apply hT
      have hs : T.det = ((Equiv.Perm.sign σ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R) * T.det) := by
        rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      rw [hs]
      exact p.mul_mem_left _ hm

/- English proof (translation)
Introduce `R _ n T p _ hT`. Take `⟨f, hf, h⟩` from `exists_injective_rows_leadingMinors_not_mem R p n T hT`. Conclude with `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun k hk => h k hk⟩`.
-/
theorem exists_rowPerm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p →
    ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n),
      ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  intro R _ n T p _ hT
  obtain ⟨f, hf, h⟩ := exists_injective_rows_leadingMinors_not_mem R p n T hT
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun k hk => h k hk⟩

end GlobalTheory
