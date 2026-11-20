import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v` using `fun s v => by`. Rewrite using `[← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]`. Unfold `Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, y, hy, hyx⟩`. Use `⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩` and prove the remaining obligations. Establish `e : s • g.symm x = y` using `g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)`. Rewrite using `[e]`.

Conclude with `hy`. Introduce and unpack `⟨z, ⟨s, hs, hz⟩, rfl⟩`. Conclude with `⟨s, hs, s • z, hz, hsm s z⟩`.
-/
theorem loc_gmap (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v := fun s v => by
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]
  unfold Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS
  ext x
  simp only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    refine ⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have e : s • g.symm x = y := g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)
    rw [e]; exact hy
  · rintro ⟨z, ⟨s, hs, hz⟩, rfl⟩
    exact ⟨s, hs, s • z, hz, hsm s z⟩

/- English proof (translation)
Introduce `L M hLM`. Unfold `Formalism.HermitianLatticesTheory.gmap at hLM`. Conclude with `Submodule.map_injective_of_injective (f := (g : V →ₗ[K] V).restrictScalars (𝓞 K)) (fun a b h => g.injective h) hLM`.
-/
theorem gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
  intro L M hLM
  unfold Formalism.HermitianLatticesTheory.gmap at hLM
  exact Submodule.map_injective_of_injective (f := (g : V →ₗ[K] V).restrictScalars (𝓞 K))
    (fun a b h => g.injective h) hLM

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.IsUnimodularAt`. Rewrite using `[he]`.
-/
theorem isUnimodularAt_of_loc_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]

end Formalism.HermitianLattices.Ext.L3
