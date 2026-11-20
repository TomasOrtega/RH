import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.ConstLat.CramerFrame

/- English proof (translation)
Introduce `F _ _ Y V`. Use `GlobalTheory.HtGen.SplitCover.isPreimmersion_j V` as an intermediate fact. Establish `hreg : ∀ (z : V.G) (f : V.X.functionField), RegAt z (fnEquiv V f) ↔ RegAt (V.j z) f`. Introduce `z f`. Rewrite using `[fnEquiv_apply]`.

Conclude with `GlobalTheory.TrueGeo.SmallSec.regAt_fnMap_iff _ _`. Use `⟨fun z f => ⟨hreg z f, ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hf : f = 0`. Substitute `hf` using the available equality. Rewrite using `[map_zero]`.

Conclude with `⟨fun h => absurd rfl h.ne_zero, fun h => absurd rfl h.ne_zero⟩`. Establish `hf' : fnEquiv V f ≠ 0` using `(map_ne_zero _).2 hf`. Rewrite using `[unitAt_iff hf, unitAt_iff hf', ← map_inv₀, hreg, hreg]`. Introduce `K _ z f h`. Rewrite using `[fnEquiv_apply]`.

Conclude with `GlobalTheory.TrueGeo.SmallSec.valAt_fnMap _ _ z h`.
-/
theorem fnEquiv_transport : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y), (∀ (z : V.G) (f : V.X.functionField), (RegAt z (fnEquiv V f) ↔ RegAt (V.j z) f) ∧ (UnitAt z (fnEquiv V f) ↔ UnitAt (V.j z) f)) ∧ ∀ {K : Type} [Field K] (z : Sp K ⟶ V.G) (f : V.X.functionField), RegAt (V.j (below z)) f → valAt z (fnEquiv V f) = valAt (z ≫ V.j) f := by
  intro F _ _ Y V
  have := GlobalTheory.HtGen.SplitCover.isPreimmersion_j V
  have hreg : ∀ (z : V.G) (f : V.X.functionField), RegAt z (fnEquiv V f) ↔ RegAt (V.j z) f := by
    intro z f
    rw [fnEquiv_apply]
    exact GlobalTheory.TrueGeo.SmallSec.regAt_fnMap_iff _ _
  refine ⟨fun z f => ⟨hreg z f, ?_⟩, ?_⟩
  · by_cases hf : f = 0
    · subst hf
      rw [map_zero]
      exact ⟨fun h => absurd rfl h.ne_zero, fun h => absurd rfl h.ne_zero⟩
    · have hf' : fnEquiv V f ≠ 0 := (map_ne_zero _).2 hf
      rw [unitAt_iff hf, unitAt_iff hf', ← map_inv₀, hreg, hreg]
  · intro K _ z f h
    rw [fnEquiv_apply]
    exact GlobalTheory.TrueGeo.SmallSec.valAt_fnMap _ _ z h

end GlobalTheory.ConstLat.CramerFrame
