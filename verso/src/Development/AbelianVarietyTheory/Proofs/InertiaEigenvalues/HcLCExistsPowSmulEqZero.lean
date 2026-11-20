import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

/- English proof (translation)
Introduce `O _ G _ _ _ M _ _ ρ ϖ hM x hx`. Take `⟨c, hc, rfl⟩` from `Submodule.mem_map.1 hx`. Establish `hlc : IsLocallyConstant (c : G → M)` using `hc`. Set `f : M → ℕ` to `fun m => Classical.choose (hM m)`. Establish `hf : ∀ m, ϖ ^ f m • m = 0` using `fun m => Classical.choose_spec (hM m)`.

Establish `hfin : (Set.range (c : G → M)).Finite` using `hlc.range_finite`. Take `⟨N, hN⟩` from `(hfin.image f).bddAbove`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `hc0 : ϖ ^ N • c = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Establish `hk : f ((c : G → M) g) ≤ N` using `hN ⟨_, ⟨g, rfl⟩, rfl⟩`. Use `show ϖ ^ N • (c : G → M) g = 0`. Rewrite using `[← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]`. Rewrite using `[← LinearMap.map_smul, hc0, map_zero]`.
-/
theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
