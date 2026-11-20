import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorContentIdealExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeVectorContentIdealExists.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.lattice_vector_content_ideal_exists : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
      ∃ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 ∧ ∀ c : E, c ∈ I ↔ c • u ∈ L := by
  first | exact @GlobalTheory.fracIdeal_of_lattice_smul_mem | exact GlobalTheory.fracIdeal_of_lattice_smul_mem | (intros; apply GlobalTheory.fracIdeal_of_lattice_smul_mem <;> assumption)
