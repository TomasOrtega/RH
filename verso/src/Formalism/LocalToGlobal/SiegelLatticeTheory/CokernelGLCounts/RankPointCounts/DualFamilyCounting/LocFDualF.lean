import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hp` using `h𝔭.isPrime`. Use `le_antisymm ?_ (LocF.le_locF 𝔭 _)` and prove the remaining obligations. Introduce `x hx`. Take `⟨t, ht, htx⟩` from `(LocF.mem_locF_iff hp _ x).1 hx`. Use `show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`.

Introduce `y hy`. Establish `e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x`. Rewrite using `[← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]`. Establish `h1` using `(show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) from htx) y hy`. Rewrite `h1` using `[e]`.

Conclude with `LIOrb.IA.mem_locF_of_smul hp ht h1`.
-/
theorem locF_dualF {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (L : Submodule (𝓞 K) V) : locF 𝔭 (dualF h 𝔭 L) = dualF h 𝔭 L := by
  have hp := h𝔭.isPrime
  refine le_antisymm ?_ (LocF.le_locF 𝔭 _)
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  have e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]
  have h1 := (show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    from htx) y hy
  rw [e] at h1
  exact LIOrb.IA.mem_locF_of_smul hp ht h1

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
