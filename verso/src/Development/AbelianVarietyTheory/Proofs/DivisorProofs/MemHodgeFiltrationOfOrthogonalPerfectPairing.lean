import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullbStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProduStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareKer

/- English proof (translation)
Introduce `hH R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ y hy`. Establish `hL` using `hP.isLB`. Take `⟨v, hv, -⟩` from `((GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hH).2.1 R B g hB hgB).1.1 y`. Establish `horth` using `GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hH R A B g hA hB hgA hgB P hL φ hφ`. Take `⟨j, hj⟩` from `GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hL`.

Establish `hc` using `GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ horth y v hv 0 (fun h hh => by rw [hy h hh, map_zero]) 0 (by rw [map_zero]; rfl) j hj`. Take `⟨k, hk⟩` from `hc`. Establish `hk' : IsCob (chartsA P) (tanCoc P j v) k`. Introduce `D _ _ D' _ _ ψ x hx`. Establish `e` using `hk D D' ψ x hx`.

Establish `h0 : fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) D D' ψ x = 0` using `rfl`. Simplify using `only [Fn1.add, Fn1.neg, h0, zero_add, neg_neg] at e`. Conclude with `e`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hL (AbDual.inl A B) hP.zero_right`. Take `⟨T, hT⟩` from `GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hL v hv.1 j hj s hs k hk'`.

Take `⟨t, ht⟩` from `GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hL v hv.1 T hT`. Establish `htriv` using `GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hL _ t ht`. Establish `hv1 : v = 1` using `hP.ker_right (epsR R) v htriv`. Substitute `hv1` using the available equality. Conclude with `isLieImage_one_iff.mp hv`.
-/
theorem mem_fil_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  intro hH R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ y hy
  have hL := hP.isLB

  obtain ⟨v, hv, -⟩ := ((GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hH).2.1 R B g hB hgB).1.1 y

  have horth := GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hH R A B g hA hB hgA hgB P hL φ hφ
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hL

  have hc := GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ horth y v hv 0
    (fun h hh => by rw [hy h hh, map_zero]) 0 (by rw [map_zero]; rfl) j hj
  obtain ⟨k, hk⟩ := hc
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    have h0 : fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) D D' ψ x = 0 := rfl
    simp only [Fn1.add, Fn1.neg, h0, zero_add, neg_neg] at e
    exact e

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hL (AbDual.inl A B) hP.zero_right

  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hL v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hL v hv.1 T hT
  have htriv := GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hL _ t ht

  have hv1 : v = 1 := hP.ker_right (epsR R) v htriv
  subst hv1
  exact isLieImage_one_iff.mp hv

end GlobalTheory.PoincareKer
