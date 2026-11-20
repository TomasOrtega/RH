import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

/- English proof (translation)
Introduce `K _ n r X T hT k hk σ`. Establish `h1 : (Matrix.of fun a l : Fin k => (X * T) (σ a) (Fin.castLE hk l)) = (Matrix.of fun a l : Fin k => X (σ a) (Fin.castLE hk l)) * (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l))`. Use extensionality with `a l`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `symm`.

Use `Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `j hj`. Establish `hlt : (Fin.castLE hk l) < j`. Assume the negation of the conclusion as `hc`. Apply `hj` to reduce the goal to its premises.

Establish `h2 : (j : ℕ) ≤ l`. Use `not_lt.1 hc` as an intermediate fact. Conclude with `this`. Conclude with `⟨⟨j, lt_of_le_of_lt h2 l.2⟩, Fin.ext rfl⟩`. Rewrite using `[hT (show id (Fin.castLE hk l) < id j from hlt), mul_zero]`.

Establish `h3 : (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l)).BlockTriangular id`. Introduce `a l h`. Conclude with `hT (show id (Fin.castLE hk l) < id (Fin.castLE hk a) from h)`. Unfold `colMinor`. Rewrite using `[h1, Matrix.det_mul, Matrix.det_of_upperTriangular h3]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.colMinor_mul_triangular :
    ∀ (K : Type) [CommRing K] (n r : ℕ) (X : Matrix (Fin n) (Fin r) K) (T : Matrix (Fin r) (Fin r) K), T.BlockTriangular id → ∀ (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n), colMinor (X * T) k hk σ = colMinor X k hk σ * ∏ i : Fin k, T (Fin.castLE hk i) (Fin.castLE hk i) := by
  intro K _ n r X T hT k hk σ
  have h1 : (Matrix.of fun a l : Fin k => (X * T) (σ a) (Fin.castLE hk l)) =
      (Matrix.of fun a l : Fin k => X (σ a) (Fin.castLE hk l)) *
        (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l)) := by
    ext a l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
    intro j hj
    have hlt : (Fin.castLE hk l) < j := by
      by_contra hc
      apply hj
      have h2 : (j : ℕ) ≤ l := by
        have := not_lt.1 hc
        exact this
      exact ⟨⟨j, lt_of_le_of_lt h2 l.2⟩, Fin.ext rfl⟩
    rw [hT (show id (Fin.castLE hk l) < id j from hlt), mul_zero]
  have h3 : (Matrix.of fun a l : Fin k => T (Fin.castLE hk a) (Fin.castLE hk l)).BlockTriangular id := by
    intro a l h
    exact hT (show id (Fin.castLE hk l) < id (Fin.castLE hk a) from h)
  unfold colMinor
  rw [h1, Matrix.det_mul, Matrix.det_of_upperTriangular h3]
  rfl
