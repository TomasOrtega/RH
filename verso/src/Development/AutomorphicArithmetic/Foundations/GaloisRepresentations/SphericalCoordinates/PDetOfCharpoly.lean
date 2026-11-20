import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma det_one_sub_smul_matrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (y : ℂ) :
    (1 - y • M).det = Polynomial.eval y M.charpoly.reverse := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, h]; ring

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.
-/
private lemma det_one_sub_smul_linear {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) (y : ℂ) :
    LinearMap.det (1 - y • f) = Polynomial.eval y f.charpoly.reverse := by
  classical
  let b := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one,
    det_one_sub_smul_matrix, LinearMap.charpoly_toMatrix]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.W2.detOfCharpoly_of :
    UpperTheory.Gal.W2.DetOfCharpoly := by
  intro V W _ _ _ _ _ _ T Θ d A h y
  rw [det_one_sub_smul_linear, det_one_sub_smul_linear, ← Polynomial.eval_mul,
    ← Polynomial.reverse_mul_of_domain, ← h, det_one_sub_smul_matrix]
