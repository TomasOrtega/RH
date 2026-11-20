import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDual
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolarizationModuleUnitDual.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.polarization_module_unit_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  first | exact @GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | exact GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | (intros; apply GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual <;> assumption)
