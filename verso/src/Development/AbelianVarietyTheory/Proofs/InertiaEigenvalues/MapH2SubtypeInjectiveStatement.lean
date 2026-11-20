import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapH2SubtypeInjective
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.map_H2_subtype_injective_of_union` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMapH2SubtypeInjective.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.map_H2_subtype_injective : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  first | exact @GlobalTheory.map_H2_subtype_injective_of_union | exact GlobalTheory.map_H2_subtype_injective_of_union | (intros; apply GlobalTheory.map_H2_subtype_injective_of_union <;> assumption)
