import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex

set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.IdxMap

/- English proof (translation)
Unfold `GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan`. Use `congr 1`. Use extensionality with `d`. Rewrite using `[GlobalTheory.BetaEx.mem_detSet]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨Matrix.of y, hy, rfl⟩`. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v, hv, rfl⟩`.
-/
theorem dets_eq_detSpan (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p L = GlobalTheory.BetaEx.detSpan L := by
  unfold GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan
  congr 1
  ext d
  rw [GlobalTheory.BetaEx.mem_detSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Matrix.of y, hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/- English proof (translation)
Introduce `F V _ _ _ _ _ _ p φ hφ L N`. Use `set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv`. Establish `hli : LinearIndependent F v` using `(Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)`. Establish `hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]`. Use `conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]`. Simplify using `[hv, map_sum, map_smul]`. Establish `hω` using `GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli`. Establish `hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v))` using `fun s t e => smul_left_injective F hω e`.

Unfold `GlobalTheory.FlatCM.idx`. Rewrite using `[hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]`.
-/
theorem idx_map_eq_colon_dets : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  intro F V _ _ _ _ _ _ p φ hφ L N
  set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv
  have hli : LinearIndependent F v :=
    (Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v := by
    refine LinearMap.ext fun x => ?_
    rw [GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]
    conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]
    simp [hv, map_sum, map_smul]
  have hω := GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli
  have hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v)) :=
    fun s t e => smul_left_injective F hω e
  unfold GlobalTheory.FlatCM.idx
  rw [hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord,
    GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]

end GlobalTheory.IdxMap
