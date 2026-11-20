import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntertwiningMapNeZeroOfIsotypicIrreducible
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoSep.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIntertwiningMapNeZeroOfIsotypicIrreducible.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  first | exact @GlobalTheory.IsoSep.main | exact GlobalTheory.IsoSep.main | (intros; apply GlobalTheory.IsoSep.main <;> assumption)
