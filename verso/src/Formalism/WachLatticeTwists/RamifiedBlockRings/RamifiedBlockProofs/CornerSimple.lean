import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Unfold `blockPoly Matrix.charpoly Matrix.charmatrix`. Set `C' : K →+* Polynomial K` to `Polynomial.C`. Establish `hUW' : U.map C' * W.map C' = e.map C'` using `by rw [← Matrix.map_mul, hUW]`. Establish `hWU' : W.map C' * U.map C' = 1`. Rewrite using `[← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]`.

Establish `hx' : (U * A * W).map C' = U.map C' * A.map C' * W.map C'`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`. Establish `h1 : (Polynomial.X : Polynomial K) • e.map C' - (U * A * W).map C' + (1 - e).map C' = 1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C')`. Establish `h2 : (1 - e).map C' = 1 - e.map C'`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [hij]`. Rewrite using `[h2, hx', ← hUW']`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, C']`.
-/
theorem blockPoly_corner {K : Type} [Field K] {d S : Type} [Fintype d] [DecidableEq d] [Fintype S]
    [DecidableEq S] (e : Matrix d d K) (U : Matrix d S K) (W : Matrix S d K) (hUW : U * W = e)
    (hWU : W * U = 1) (A : Matrix S S K) : blockPoly e (U * A * W) = A.charpoly := by
  unfold blockPoly Matrix.charpoly Matrix.charmatrix
  let C' : K →+* Polynomial K := Polynomial.C
  have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
  have hWU' : W.map C' * U.map C' = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
  have hx' : (U * A * W).map C' = U.map C' * A.map C' * W.map C' := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
  have h1 : (Polynomial.X : Polynomial K) • e.map C' - (U * A * W).map C' + (1 - e).map C' =
      1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
    have h2 : (1 - e).map C' = 1 - e.map C' := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [h2, hx', ← hUW']
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, C']

/- English proof (translation)
Introduce `K _ _ d _ _ m c P e hP he hblk`. Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hdet`. Establish `hPP' : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Take `⟨f, hf⟩ : ∃ f, f = P * e * P⁻¹` from `⟨_, rfl⟩`.

Rewrite `hblk` using `[← hf]`. Establish `hff : f * f = f`. Establish `: P * e * P⁻¹ * (P * e * P⁻¹) = P * (e * (P⁻¹ * P) * e) * P⁻¹`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hf, this, hPP', Matrix.mul_one, he]`.

Establish `hef : e = P⁻¹ * f * P`. Establish `: P⁻¹ * (P * e * P⁻¹) * P = (P⁻¹ * P) * e * (P⁻¹ * P)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[hf, this, hPP', Matrix.one_mul, Matrix.mul_one]`. Set `σ : (Σ i, {a // c a = i}) ≃ d` to `Equiv.sigmaFiberEquiv c`. Establish `hfb : f.submatrix σ σ = Matrix.blockDiagonal' (fun i => f.toSquareBlock c i)`.

Use extensionality with `⟨i, a⟩ ⟨j, b⟩`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.blockDiagonal'_apply_eq]`. Both sides reduce to the same expression.

Rewrite using `[Matrix.blockDiagonal'_apply_ne _ _ _ h]`. Conclude with `hblk _ _ (by show c a.1 ≠ c b.1; rw [a.2, b.2]; exact h)`. Establish `hidem : ∀ i, f.toSquareBlock c i * f.toSquareBlock c i = f.toSquareBlock c i`. Establish `h1 : Matrix.blockDiagonal' (fun i => f.toSquareBlock c i * f.toSquareBlock c i) = Matrix.blockDiagonal' (fun i => f.toSquareBlock c i)`. Rewrite using `[Matrix.blockDiagonal'_mul, ← hfb, Matrix.submatrix_mul_equiv, hff]`.

Introduce `i`. Conclude with `congrFun (Matrix.blockDiagonal'_injective h1) i`. Use `choose S hS1 hS2 U W hUW hWU using fun i => idem_factor (f.toSquareBlock c i) (hidem i)`. Set `v : (Σ i, S i) ↪ K` to `((Fintype.equivFin (Σ i, S i)).toEmbedding.trans Fin.valEmbedding).trans (Infinite.natEmbedding K)`. Set `U0 : Matrix d (Σ i, S i) K` to `(Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _)`.

Set `W0 : Matrix (Σ i, S i) d K` to `(Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm`. Establish `hU0W0 : U0 * W0 = f` using `by show (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) * (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm = f`. Rewrite using `[Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, funext hUW, ← hfb]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.

Establish `hW0U0 : W0 * U0 = 1` using `by show (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm * (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) = 1`. Establish `h1 : (fun i => W i * U i) = 1` using `funext hWU`. Rewrite using `[Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, h1, Matrix.blockDiagonal'_one]`. Conclude with `Matrix.submatrix_one_equiv _`. Establish `hB : U0 * Matrix.diagonal v * W0 = (Matrix.blockDiagonal' (fun i => U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)).submatrix σ.symm σ.symm`.

Rewrite using `[Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_diagonal]`. Use extensionality with `a b`. Both sides reduce to the same expression. Use `⟨P⁻¹ * (U0 * Matrix.diagonal v * W0) * P, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Establish `h1 : P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * P⁻¹ = (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[h1, hPP, Matrix.one_mul, Matrix.mul_one, hB]`. Use `show Matrix.blockDiagonal' (fun i => U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i) ⟨c a, ⟨a, rfl⟩⟩ ⟨c b, ⟨b, rfl⟩⟩ = 0`. Conclude with `Matrix.blockDiagonal'_apply_ne _ _ _ hab`. Establish `h1 : e * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * e = (P⁻¹ * U0) * Matrix.diagonal v * (W0 * P)`.

Establish `h2 : P⁻¹ * f * P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * (P⁻¹ * f * P) = P⁻¹ * (f * (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) * f) * P`. Simplify using `only [Matrix.mul_assoc]`. Establish `h3 : U0 * W0 * (U0 * Matrix.diagonal v * W0) * (U0 * W0) = U0 * ((W0 * U0) * Matrix.diagonal v * (W0 * U0)) * W0`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hef, h2, hPP, Matrix.mul_one, Matrix.mul_one, ← hU0W0, h3, hW0U0, Matrix.one_mul, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `h4 : (P⁻¹ * U0) * (W0 * P) = e`. Establish `: (P⁻¹ * U0) * (W0 * P) = P⁻¹ * (U0 * W0) * P` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hU0W0, ← hef]`. Establish `h5 : (W0 * P) * (P⁻¹ * U0) = 1`.

Establish `: (W0 * P) * (P⁻¹ * U0) = W0 * (P * P⁻¹) * U0` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hPP, Matrix.mul_one, hW0U0]`. Rewrite using `[h1, blockPoly_corner e _ _ h4 h5, Matrix.charpoly_diagonal]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.mpr v.injective`.
-/
theorem cornerSimple : StatCornerSimple := by
  intro K _ _ d _ _ m c P e hP he hblk
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨f, hf⟩ : ∃ f, f = P * e * P⁻¹ := ⟨_, rfl⟩
  rw [← hf] at hblk
  have hff : f * f = f := by
    have : P * e * P⁻¹ * (P * e * P⁻¹) = P * (e * (P⁻¹ * P) * e) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.mul_one, he]
  have hef : e = P⁻¹ * f * P := by
    have : P⁻¹ * (P * e * P⁻¹) * P = (P⁻¹ * P) * e * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [hf, this, hPP', Matrix.one_mul, Matrix.mul_one]
  let σ : (Σ i, {a // c a = i}) ≃ d := Equiv.sigmaFiberEquiv c
  have hfb : f.submatrix σ σ = Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact hblk _ _ (by show c a.1 ≠ c b.1; rw [a.2, b.2]; exact h)
  have hidem : ∀ i, f.toSquareBlock c i * f.toSquareBlock c i = f.toSquareBlock c i := by
    have h1 : Matrix.blockDiagonal' (fun i => f.toSquareBlock c i * f.toSquareBlock c i) =
        Matrix.blockDiagonal' (fun i => f.toSquareBlock c i) := by
      rw [Matrix.blockDiagonal'_mul, ← hfb, Matrix.submatrix_mul_equiv, hff]
    intro i
    exact congrFun (Matrix.blockDiagonal'_injective h1) i
  choose S hS1 hS2 U W hUW hWU using fun i => idem_factor (f.toSquareBlock c i) (hidem i)
  let v : (Σ i, S i) ↪ K :=
    ((Fintype.equivFin (Σ i, S i)).toEmbedding.trans Fin.valEmbedding).trans (Infinite.natEmbedding K)
  let U0 : Matrix d (Σ i, S i) K := (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _)
  let W0 : Matrix (Σ i, S i) d K := (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm
  have hU0W0 : U0 * W0 = f := by
    show (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) *
      (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm = f
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, funext hUW, ← hfb]
    ext a b
    simp
  have hW0U0 : W0 * U0 = 1 := by
    show (Matrix.blockDiagonal' W).submatrix (Equiv.refl _) σ.symm *
      (Matrix.blockDiagonal' U).submatrix σ.symm (Equiv.refl _) = 1
    have h1 : (fun i => W i * U i) = 1 := funext hWU
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, h1, Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv _
  have hB : U0 * Matrix.diagonal v * W0 = (Matrix.blockDiagonal' (fun i =>
      U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)).submatrix σ.symm σ.symm := by
    rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_diagonal]
    ext a b
    rfl
  refine ⟨P⁻¹ * (U0 * Matrix.diagonal v * W0) * P, ?_, ?_⟩
  · intro a b hab
    have h1 : P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * P⁻¹ =
        (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [h1, hPP, Matrix.one_mul, Matrix.mul_one, hB]
    show Matrix.blockDiagonal' (fun i => U i * Matrix.diagonal (fun s => v ⟨i, s⟩) * W i)
      ⟨c a, ⟨a, rfl⟩⟩ ⟨c b, ⟨b, rfl⟩⟩ = 0
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  · have h1 : e * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * e =
        (P⁻¹ * U0) * Matrix.diagonal v * (W0 * P) := by
      have h2 : P⁻¹ * f * P * (P⁻¹ * (U0 * Matrix.diagonal v * W0) * P) * (P⁻¹ * f * P) =
          P⁻¹ * (f * (P * P⁻¹) * (U0 * Matrix.diagonal v * W0) * (P * P⁻¹) * f) * P := by
        simp only [Matrix.mul_assoc]
      have h3 : U0 * W0 * (U0 * Matrix.diagonal v * W0) * (U0 * W0) =
          U0 * ((W0 * U0) * Matrix.diagonal v * (W0 * U0)) * W0 := by
        simp only [Matrix.mul_assoc]
      rw [hef, h2, hPP, Matrix.mul_one, Matrix.mul_one, ← hU0W0, h3, hW0U0, Matrix.one_mul,
        Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    have h4 : (P⁻¹ * U0) * (W0 * P) = e := by
      have : (P⁻¹ * U0) * (W0 * P) = P⁻¹ * (U0 * W0) * P := by simp only [Matrix.mul_assoc]
      rw [this, hU0W0, ← hef]
    have h5 : (W0 * P) * (P⁻¹ * U0) = 1 := by
      have : (W0 * P) * (P⁻¹ * U0) = W0 * (P * P⁻¹) * U0 := by simp only [Matrix.mul_assoc]
      rw [this, hPP, Matrix.mul_one, hW0U0]
    rw [h1, blockPoly_corner e _ _ h4 h5, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr v.injective

end Formalism.RepresentationBoundsCohomology.ringDataObjects
