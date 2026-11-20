import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselian
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_strictHenselisation_of_henselian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsStrictHenselisationOfHenselian.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_etale_localization_filtration_strictHenselization : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.exists_strictHenselisation_of_henselian | exact GlobalTheory.exists_strictHenselisation_of_henselian | (intros; apply GlobalTheory.exists_strictHenselisation_of_henselian <;> assumption)
