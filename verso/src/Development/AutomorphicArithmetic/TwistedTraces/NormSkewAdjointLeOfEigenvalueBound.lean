import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `E _ _ _ D M hskew hev x`. Establish `hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric`. Introduce `x y`. Establish `h` using `hskew x y`. Simplify using `only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]`.

Take the linear combination `(-Complex.I) * h`. Establish `hn : Module.finrank ℂ E = Module.finrank ℂ E` using `rfl`. Establish `hb : ∀ i, |hT.eigenvalues hn i| ≤ M`. Introduce `i`. Establish `h1` using `hT.apply_eigenvectorBasis hn i`.

Establish `h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i`. Establish `h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i))`. Rewrite using `[LinearMap.smul_apply, smul_smul]`. Simplify using the standard rewrite rules. Rewrite using `[h3, h1, smul_smul]`.

Both sides reduce to the same expression. Establish `h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ))` using `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩`. Establish `h5` using `hev _ h4`. Simplify using `using h5`. Break down `subsingleton_or_nontrivial E with hE | hE` into its components or cases.

Establish `: x = 0` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `hM : 0 ≤ M` using `(abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)`. Establish `hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖`.

Simplify using `[norm_smul]`. Rewrite using `[hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x), ← (hT.eigenvectorBasis hn).repr.norm_map x]`. Apply `abs_le_of_sq_le_sq' _ (by positivity) |>.2` to reduce the goal to its premises. Rewrite using `[mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `i _`. Establish `h6` using `hT.eigenvectorBasis_apply_self_apply hn x i`. Rewrite using `[h6, norm_mul, mul_pow]`. Use `gcongr`. Simplify using `using hb i`.
-/
theorem UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (D : Module.End ℂ E) (M : ℝ), (∀ x y, inner ℂ (D x) y + inner ℂ x (D y) = 0) → (∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ D M hskew hev x
  have hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    have h := hskew x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (-Complex.I) * h
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  have hb : ∀ i, |hT.eigenvalues hn i| ≤ M := by
    intro i
    have h1 := hT.apply_eigenvectorBasis hn i
    have h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i := by
      have h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i)) := by
        rw [LinearMap.smul_apply, smul_smul]; simp
      rw [h3, h1, smul_smul]; rfl
    have h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩
    have h5 := hev _ h4
    simpa using h5
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)
  have hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖ := by
    simp [norm_smul]
  rw [hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x),
    ← (hT.eigenvectorBasis hn).repr.norm_map x]
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h6 := hT.eigenvectorBasis_apply_self_apply hn x i
  rw [h6, norm_mul, mul_pow]
  gcongr
  simpa using hb i
