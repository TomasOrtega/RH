import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StrictHensel.strictlyHenselian_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStrictlyHenselianIff.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime], q.comap (algebraMap R A) = maximalIdeal R → ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔ (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  first | exact @GlobalTheory.StrictHensel.strictlyHenselian_iff | exact GlobalTheory.StrictHensel.strictlyHenselian_iff | (intros; apply GlobalTheory.StrictHensel.strictlyHenselian_iff <;> assumption)
