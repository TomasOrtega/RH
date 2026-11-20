import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

/- English proof (translation)
Use `set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM`. Set `K : Submodule ℝ (EuclideanSpace ℝ (Fin g))` to `LinearMap.ker (Matrix.toEuclideanLin M)`. Set `P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g)` to `(K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))`. Set `Pr : Matrix (Fin g) (Fin g) ℝ` to `Matrix.toEuclideanLin.symm P`. Establish `hPr : Matrix.toEuclideanLin Pr = P` using `LinearEquiv.apply_symm_apply _ _`.

Establish `hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v))`. Introduce `v`. Rewrite using `[← hPr, Matrix.toEuclideanLin_apply]`. Establish `hidem : ∀ x, P (P x) = P x`. Introduce `x`.

Establish `hx : K.starProjection x ∈ K` using `Submodule.starProjection_apply_mem K x`. Conclude with `(Submodule.starProjection_eq_self_iff).2 hx`. Use `⟨Pr, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv, WithLp.toLp_ofLp, hidem]`. Establish `hs : Pr.IsHermitian`. Rewrite using `[Matrix.isHermitian_iff_isSymmetric, hPr]`. Conclude with `Submodule.starProjection_isSymmetric K`. Simplify `hs.eq` using `[Matrix.conjTranspose_eq_transpose_of_trivial]`.

Introduce `v`. Rewrite using `[hmv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hk : WithLp.toLp 2 v ∈ K`.

Establish `h' : M *ᵥ v = 0` using `h`. Rewrite using `[LinearMap.mem_ker, Matrix.toEuclideanLin_apply]`. Simplify using `[h']`. Establish `: P (WithLp.toLp 2 v) = WithLp.toLp 2 v` using `(Submodule.starProjection_eq_self_iff).2 hk`. Rewrite using `[this]`.

Introduce `h`. Establish `h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v`. Rewrite using `[← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]`. Establish `hk : WithLp.toLp 2 v ∈ K` using `(Submodule.starProjection_eq_self_iff).1 h1`. Rewrite `hk` using `[LinearMap.mem_ker, Matrix.toEuclideanLin_apply]`.

Establish `h' : M *ᵥ v = 0` using `by simpa using hk`. Conclude with `h'`.
-/
theorem exists_isKerProj (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) :
    ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  classical
  set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin g)) := LinearMap.ker (Matrix.toEuclideanLin M)
  let P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))
  let Pr : Matrix (Fin g) (Fin g) ℝ := Matrix.toEuclideanLin.symm P
  have hPr : Matrix.toEuclideanLin Pr = P := LinearEquiv.apply_symm_apply _ _
  have hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v)) := by
    intro v
    rw [← hPr, Matrix.toEuclideanLin_apply]
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hx : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact (Submodule.starProjection_eq_self_iff).2 hx
  refine ⟨Pr, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv,
      WithLp.toLp_ofLp, hidem]
  · have hs : Pr.IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymmetric, hPr]
      exact Submodule.starProjection_isSymmetric K
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  · intro v
    rw [hmv]
    constructor
    · intro h
      have hk : WithLp.toLp 2 v ∈ K := by
        have h' : M *ᵥ v = 0 := h
        rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply]
        simp [h']
      have : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := (Submodule.starProjection_eq_self_iff).2 hk
      rw [this]
    · intro h
      have h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
        rw [← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]
      have hk : WithLp.toLp 2 v ∈ K := (Submodule.starProjection_eq_self_iff).1 h1
      rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply] at hk
      have h' : M *ᵥ v = 0 := by simpa using hk
      exact h'

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
