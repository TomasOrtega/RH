import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThickeningSectionHomogeneousForm.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.thickening_section_homogeneous_form : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ker_thickι_chart | exact GlobalTheory.CompanionTheory.GE.ker_thickι_chart | (intros; apply GlobalTheory.CompanionTheory.GE.ker_thickι_chart <;> assumption)
