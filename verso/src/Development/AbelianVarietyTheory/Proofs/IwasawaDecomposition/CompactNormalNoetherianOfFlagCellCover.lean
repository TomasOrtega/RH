import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

/- English proof (translation)
Establish `: IsNoetherianRing Γ(X, U.1)` using `IsLocallyNoetherian.component_noetherian U`. Establish `: IsNoetherianRing (CR m U)` using `inferInstance`. Conclude with `inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (CR m U)))`.
-/
theorem noetherianSpace_cell {X : Scheme.{0}} [IsLocallyNoetherian X] {T : Type} [Finite T] (m : T → ℕ)
    (U : X.affineOpens) : TopologicalSpace.NoetherianSpace (Sp (CR m U)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing (CR m U) := inferInstance
  exact inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (CR m U)))

/- English proof (translation)
Introduce `X _ T _ m B _ V F i hX hi hc`. Establish `hN : TopologicalSpace.NoetherianSpace F`. Establish `h1 : ∀ a : B × Pm m, TopologicalSpace.NoetherianSpace (Set.range (i a.1 a.2))` using `fun a => by`. Use `noetherianSpace_cell m (V a.1)` as an intermediate fact. Conclude with `TopologicalSpace.NoetherianSpace.range _ (i a.1 a.2).continuous`.

Establish `h2` using `TopologicalSpace.NoetherianSpace.iUnion (fun a : B × Pm m => Set.range (i a.1 a.2))`. Establish `h3 : (⋃ a : B × Pm m, Set.range (i a.1 a.2)) = Set.univ`. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨b, w, h⟩` from `hc x`. Conclude with `Set.mem_iUnion.2 ⟨(b, w), h⟩`.

Rewrite `h2` using `[h3]`. Conclude with `TopologicalSpace.noetherian_univ_iff.1 h2`. Use `⟨inferInstance, fun x => ?_, hN⟩` and prove the remaining obligations. Take `⟨b, w, y, rfl⟩` from `hc x`. Use `hi b w` as an intermediate fact.

Take `⟨_, _⟩` from `(cell_smooth_normal X T m (V b) hX).2 y`. Set `e` to `(asIso ((i b w).stalkMap y)).commRingCatIsoToRingEquiv`. Conclude with `⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩`.
-/
theorem compact_normal_noetherian_of_cells : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  intro X _ T _ m B _ V F i hX hi hc
  have hN : TopologicalSpace.NoetherianSpace F := by
    have h1 : ∀ a : B × Pm m, TopologicalSpace.NoetherianSpace (Set.range (i a.1 a.2)) := fun a => by
      have := noetherianSpace_cell m (V a.1)
      exact TopologicalSpace.NoetherianSpace.range _ (i a.1 a.2).continuous
    have h2 := TopologicalSpace.NoetherianSpace.iUnion (fun a : B × Pm m => Set.range (i a.1 a.2))
    have h3 : (⋃ a : B × Pm m, Set.range (i a.1 a.2)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨b, w, h⟩ := hc x
      exact Set.mem_iUnion.2 ⟨(b, w), h⟩
    rw [h3] at h2
    exact TopologicalSpace.noetherian_univ_iff.1 h2
  refine ⟨inferInstance, fun x => ?_, hN⟩
  obtain ⟨b, w, y, rfl⟩ := hc x
  have := hi b w
  obtain ⟨_, _⟩ := (cell_smooth_normal X T m (V b) hX).2 y
  let e := (asIso ((i b w).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end GlobalTheory.FlagEmb
