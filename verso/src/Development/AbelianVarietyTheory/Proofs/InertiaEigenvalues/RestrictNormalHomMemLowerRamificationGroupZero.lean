import Mathlib
import GroundTheory.LocalFields.Examples
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `l _ L _ _ _ _ _ _ _ _ _ _ σ hσ`. Rewrite using `[mem_lowerRamificationGroup_iff]`. Introduce `x`. Establish `h01 : ((0 : ℤ) + 1).toNat = 1` using `rfl`. Rewrite using `[h01, pow_one]`.

Establish `hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1` using `((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L (x : L)).1).1 x.2`. Establish `hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L))` using `AlgEquiv.restrictNormal_commutes σ L (x : L)`. Establish `hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1`. Rewrite using `[(GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).2, map_sub, hc]`. Conclude with `hσ _ hx`.

Introduce `hu`. Establish `h1` using `(Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu`. Establish `h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)` using `rfl`. Express the relevant statement in the definitionally equal form `valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1`. Rewrite `h1` using `[h2]`.

Conclude with `hlt.ne h1`.
-/
theorem restrictNormalHom_mem_lowerRamificationGroup_zero : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (σ : GQ l), (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → AlgEquiv.restrictNormalHom L σ ∈ lowerRamificationGroup ℚ_[l] L 0 := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ σ hσ
  rw [mem_lowerRamificationGroup_iff]
  intro x
  have h01 : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [h01, pow_one]
  have hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1 := ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L (x : L)).1).1 x.2
  have hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L)) :=
    AlgEquiv.restrictNormal_commutes σ L (x : L)
  have hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1 := by
    rw [(GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).2, map_sub, hc]
    exact hσ _ hx
  intro hu
  have h1 := (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu
  have h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - (x : L) := rfl
  change valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1
  rw [h2] at h1
  exact hlt.ne h1

end GlobalTheory.PMon.Ram
