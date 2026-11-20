import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndex
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicLatticeOrderCoprimeIndex.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.adelic_lattice_order_coprime_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime →
    ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
    ∃ n : ℕ, n.Coprime l ∧ (∀ x ∈ lattice c y, (n : E) * x ∈ orderC c) ∧ ∀ x ∈ orderC c, (n : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.CMVal.LatLoc.lattice_near_orderC | exact GlobalTheory.CMVal.LatLoc.lattice_near_orderC | (intros; apply GlobalTheory.CMVal.LatLoc.lattice_near_orderC <;> assumption)
