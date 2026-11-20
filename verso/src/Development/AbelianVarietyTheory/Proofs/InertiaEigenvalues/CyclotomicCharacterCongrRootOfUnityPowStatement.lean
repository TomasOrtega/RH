import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicCharacterCongrRootOfUnityPow.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow : ∀ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ), ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) = PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | exact GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | (intros; apply GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr <;> assumption)
