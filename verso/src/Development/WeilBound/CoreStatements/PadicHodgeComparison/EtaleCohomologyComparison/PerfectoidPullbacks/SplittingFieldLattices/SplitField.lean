import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasisBOfBcOn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapOAffine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgPullSqC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseLimitCohomologyComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem split_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := @GlobalTheory.CompanionTheory.LecShift.leC_shift

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bc_loc : KH.LocBc → KH.PolyTf → BcOn True := @GlobalTheory.CompanionTheory.BcLoc.bc_single

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bc_glob : KH.GlobBcSt → BcOn True → BcOn False := @GlobalTheory.CompanionTheory.GlobBc.main

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fin_o : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := @GlobalTheory.CompanionTheory.FinOverO.finO

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem afg_a : BcOn False → FinO → AfgA := @GlobalTheory.CompanionTheory.LatticeFinite.afgA_of_bcOn_finO

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lift_a : AfgA → LiftA := @GlobalTheory.CompanionTheory.LiftLat.liftA_of_afgA

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem basis_b : BcOn False → KH.KIso → BasisB := @GlobalTheory.CompanionTheory.BasisBase.basisB_of_bcOn

end CrystallineSemistableComparison.Pb
