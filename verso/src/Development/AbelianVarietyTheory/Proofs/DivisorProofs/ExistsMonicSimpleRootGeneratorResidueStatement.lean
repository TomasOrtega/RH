import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicSimpleRootGeneratorResidue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_monic_simple_root_generator_residue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMonicSimpleRootGeneratorResidue.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_monic_simple_root_generating_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R'] [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' → ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧ (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧ ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  first | exact @GlobalTheory.exists_monic_simple_root_generator_residue | exact GlobalTheory.exists_monic_simple_root_generator_residue | (intros; apply GlobalTheory.exists_monic_simple_root_generator_residue <;> assumption)
