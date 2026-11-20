import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativePreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasFiniteLengthOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrreducibleOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotientStatement

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hi` using `τ.irr`. Assume the negation of the conclusion as `hs`. Rewrite `hs` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises.

Use extensionality with `x`. Rewrite using `[Subsingleton.elim x 0]`. Conclude with `⟨fun _ => zero_mem _, fun _ => zero_mem _⟩`.
-/
theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

/- English proof (translation)
Establish `: (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a)` using `funext fun a => AddChar.inv_apply ψ a`. Rewrite using `[this]`. Conclude with `hc.comp continuous_neg`.
-/
theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
