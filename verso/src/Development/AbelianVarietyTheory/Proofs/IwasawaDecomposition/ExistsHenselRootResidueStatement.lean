import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidue
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsHenselRootResidue.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_hensel_root_residue : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V) (σ : ResidueField R →+* ResidueField V), (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) → ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by
  first | exact @GlobalTheory.exists_root_lift_of_residue_map | exact GlobalTheory.exists_root_lift_of_residue_map | (intros; apply GlobalTheory.exists_root_lift_of_residue_map <;> assumption)
