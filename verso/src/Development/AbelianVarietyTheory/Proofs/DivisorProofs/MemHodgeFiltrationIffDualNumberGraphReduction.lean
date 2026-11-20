import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

/- English proof (translation)
Rewrite using `[GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀) (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]`. Conclude with `Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)`.
-/
theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨d, hd⟩` from `exists_crys hA y (f y)`. Use `⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(isBC_constMor hA).2 c`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, TrivSqZeroExt.fst_zero]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb, TrivSqZeroExt.fst_add]`. Consider the case `tmul a c`. Rewrite using `[liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨d, ⟨x, hx, y', -, e⟩, hc⟩`. Establish `: y = x` using `LinearMap.ext fun c ↦ by`. Establish `h1` using `hc ((constMor A₀).pull c)`. Rewrite `h1` using `[crysRed_pull_constMor_pull, e c]`.

Simplify using `using h1`. Conclude with `this ▸ hx`.
-/
theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add, ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
