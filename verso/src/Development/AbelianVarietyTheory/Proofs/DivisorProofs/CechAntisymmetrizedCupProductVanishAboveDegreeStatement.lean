import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechAntisymmetrizedCupProductVanishAboveDegree.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  first | exact @GlobalTheory.DI.alt_and_phi_vanish_above_degree | exact GlobalTheory.DI.alt_and_phi_vanish_above_degree | (intros; apply GlobalTheory.DI.alt_and_phi_vanish_above_degree <;> assumption)
