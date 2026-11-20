import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
