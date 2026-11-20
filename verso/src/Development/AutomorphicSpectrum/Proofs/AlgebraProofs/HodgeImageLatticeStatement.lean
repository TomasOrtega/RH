import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHodgeImageLattice.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.hodge_image_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main <;> assumption)
