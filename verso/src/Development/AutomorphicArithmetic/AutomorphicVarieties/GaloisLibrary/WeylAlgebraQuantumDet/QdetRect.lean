import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `n d d' E E' A h u`. Establish `hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A = A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v`. Introduce `v`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]`. Establish `hT : ∀ (v : ℂ) a b, Formalism.REAL.Tm E v a b * A = A * Formalism.REAL.Tm E' v a b`.

Introduce `v a b`. Simplify using `only [Formalism.REAL.Tm]`. Rewrite using `[Matrix.add_mul, Matrix.mul_add, h]`. Use `split_ifs`. Rewrite using `[hs]`.

Rewrite using `[Matrix.zero_mul, Matrix.mul_zero]`. Establish `hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ), (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro f g _`.

Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `f g hfg`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc, ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]`. Establish `hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ)`.

Introduce `z`. Rewrite using `[← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)), ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]`. Conclude with `hs _`. Simplify using `only [Formalism.REAL.qdet, Formalism.REAL.qminor]`. Rewrite using `[Matrix.sum_mul, Matrix.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]`.
-/
theorem UpperTheory.V.Weyl.qdetRect :
    ∀ (n d d' : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (E' : Fin n → Fin n → Matrix (Fin d') (Fin d') ℂ)
      (A : Matrix (Fin d) (Fin d') ℂ), (∀ a b, E a b * A = A * E' a b) → ∀ u : ℂ, Formalism.REAL.qdet E u * A = A * Formalism.REAL.qdet E' u := by
  intro n d d' E E' A h u
  have hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A = A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hT : ∀ (v : ℂ) a b, Formalism.REAL.Tm E v a b * A = A * Formalism.REAL.Tm E' v a b := by
    intro v a b
    simp only [Formalism.REAL.Tm]
    rw [Matrix.add_mul, Matrix.mul_add, h]
    split_ifs
    · rw [hs]
    · rw [Matrix.zero_mul, Matrix.mul_zero]
  have hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ),
      (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod := by
    intro m
    induction m with
    | zero => intro f g _; simp
    | succ m ih =>
      intro f g hfg
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc,
        ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]
  have hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ) := by
    intro z
    rw [← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)), ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]
    exact hs _
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]
