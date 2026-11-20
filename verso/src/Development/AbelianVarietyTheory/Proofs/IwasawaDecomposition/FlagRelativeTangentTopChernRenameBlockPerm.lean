import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.RootDiscrPerm

/- English proof (translation)
Rewrite using `[Matrix.det_vandermonde]`. Conclude with `Finset.prod_comm' (fun j i => by simp [and_comm])`.
-/
theorem prod_Iio_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i)) = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

/- English proof (translation)
Establish `h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id`. Use extensionality with `i k`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[h, Matrix.det_permute]`.
-/
theorem det_vandermonde_comp_perm {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    (Matrix.vandermonde (fun i => v (σ i))).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

/- English proof (translation)
Unfold `rootDiscr`. Conclude with `Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _`.
-/
theorem rootDiscr_eq_prod_det (ι : Type) [Fintype ι] (m : ι → ℕ) :
    rootDiscr m = ∏ τ, (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
  unfold rootDiscr
  exact Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _

end GlobalTheory.GoodMetric.RootDiscrPerm

open GlobalTheory.GoodMetric.RootDiscrPerm in
/- English proof (translation)
Introduce `ι _ m w`. Rewrite using `[rootDiscr_eq_prod_det, map_prod]`. Establish `h : ∀ τ, rename (Equiv.sigmaCongrRight w) (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det = ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det`. Introduce `τ`. Rewrite using `[AlgHom.map_det]`.

Establish `e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) = Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ))`. Use extensionality with `i k`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[e]`. Conclude with `det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)`.

Rewrite using `[Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  intro ι _ m w
  rw [rootDiscr_eq_prod_det, map_prod]
  have h : ∀ τ, rename (Equiv.sigmaCongrRight w)
      (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det =
      ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    have e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix
        (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) =
        Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ)) := by
      ext i k; simp [Matrix.vandermonde_apply]
    rw [e]
    exact det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)
  rw [Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]
  push_cast
  rfl
