import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeIsRootOfSimpleRootPointedEtaleNbhd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLeIsRootOfSimpleRootPointedEtaleNbhd.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (h : Polynomial i.A) (a₀ : i.A), h.Monic → i.pt (h.eval a₀) = 0 → i.pt (h.derivative.eval a₀) ≠ 0 → ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B), (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧ c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  first | exact @GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | exact GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | (intros; apply GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root <;> assumption)
