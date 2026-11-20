import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

/- English proof (translation)
Introduce `hA`. Establish `h` using `Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅`. Rewrite `h` using `[Filter.eventually_cofinite]`. Use `h.subset fun p hp => ?_` and prove the remaining obligations. Introduce `hg`.

Apply `hp` to reduce the goal to its premises. Establish `hδ : δ p ≠ 0` using `(hA p).2.1`. Establish `hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))` using `(isUnit_iff_ne_zero.2 hδ).map _`. Establish `e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hδ, map_one]`.

Establish `hinv : Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (algebraMap _ _ (δ p)), e1, mul_one]`. Use `_ = (Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by`. Rewrite using `[mul_assoc]`.

Use `_ = _ := by rw [Ring.inverse_mul_cancel _ hu, one_mul]`. Rewrite using `[hinv, (D.s.atP p).O_def]`. Establish `hmem : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]` using `hg.2.1.2`. Establish `: algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨(δ p)⁻¹, hmem⟩` using `rfl`. Rewrite using `[this]`.

Conclude with `isIntegral_algebraMap`.
-/
theorem deltaAE_holds (D : D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : DeltaAE D δ M := by
  intro hA
  have h := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun p hp => ?_
  intro hg
  apply hp
  have hδ : δ p ≠ 0 := (hA p).2.1
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) := (isUnit_iff_ne_zero.2 hδ).map _
  have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  have hinv : Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
    calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))
        = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) := by
          rw [mul_comm (algebraMap _ _ (δ p)), e1, mul_one]
      _ = (Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hinv, (D.s.atP p).O_def]
  have hmem : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := hg.2.1.2
  have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨(δ p)⁻¹, hmem⟩ := rfl
  rw [this]
  exact isIntegral_algebraMap

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
