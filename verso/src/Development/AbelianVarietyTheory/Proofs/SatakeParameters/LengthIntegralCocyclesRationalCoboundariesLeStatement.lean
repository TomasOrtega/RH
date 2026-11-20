import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLe
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLengthIntegralCocyclesRationalCoboundariesLe.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.cocycle_bound_length_le | exact GlobalTheory.cocycle_bound_length_le | (intros; apply GlobalTheory.cocycle_bound_length_le <;> assumption)
