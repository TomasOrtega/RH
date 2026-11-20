import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisation
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Henselisation.exists_henselisation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHenselisation.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_etale_localization_filtration_henselization : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.Henselisation.exists_henselisation | exact GlobalTheory.Henselisation.exists_henselisation | (intros; apply GlobalTheory.Henselisation.exists_henselisation <;> assumption)
