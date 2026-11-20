import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspRep.CompUniq.isotypic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIrreducibleRepIsotypicOfCentraliserFactor.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  first | exact @GlobalTheory.CuspRep.CompUniq.isotypic | exact GlobalTheory.CuspRep.CompUniq.isotypic | (intros; apply GlobalTheory.CuspRep.CompUniq.isotypic <;> assumption)
