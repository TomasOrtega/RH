import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows posDef_dual)
open GlobalTheory.SepRows
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopLineProof

/- English proof (translation)
Establish `hl₀ : l₀ ≠ 0`. Introduce and unpack `rfl`. Use `hne (LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_)` and prove the remaining obligations. Simplify using `[hb₀]`. Use `LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, hb, hb₀, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem bilin_prop {X Y ι κ : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (fx : ι → X) (fy : κ → Y)
    (hx : Submodule.span ℂ (Set.range fx) = ⊤) (hy : Submodule.span ℂ (Set.range fy) = ⊤) (b b₀ : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (f : ι → κ → ℂ) (l l₀ : ℂ) (hb : ∀ i j, b (fx i) (fy j) = f i j * l) (hb₀ : ∀ i j, b₀ (fx i) (fy j) = f i j * l₀)
    (hne : b₀ ≠ 0) : b = (l / l₀) • b₀ := by
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_)
    simp [hb₀]
  refine LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hb, hb₀, smul_eq_mul]
  field_simp

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Take `⟨hc, hs⟩` from `GlobalTheory.CoefModel.realGL_laws hθ (G.V (.top 0))`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))`. Use `GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)` and prove the remaining obligations. Establish `: GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h = 1` using `funext fun τ => by show Formalism.UG.bc (θ τ) (infHom (G.V (.top 0)) h) = 1`. Rewrite using `[show infHom (G.V (.top 0)) h = 1 from hh, map_one]`.

Rewrite using `[MonoidHom.comp_apply, this, map_one]`. Conclude with `GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h τ) (GlobalTheory.RecDictModel.archM_unitary (G.V (.top 0)) (hθ τ) h)`. Use `((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_ show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹ τ : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = _` and prove the remaining obligations. Rewrite using `[map_inv]`. Both sides reduce to the same expression.

Take `⟨h, e⟩` from `hs (invTrK g) fun τ => by`. Use `GlobalTheory.CoefModel.invTr_unitary (hg τ)` as an intermediate fact. Rewrite `this` using `[← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.FunObj.posDef_Xp G (tauE D τ)).isUnit), Matrix.transpose_transpose]`. Then use the resulting hypothesis. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, e]`.

Conclude with `funext fun τ => GlobalTheory.CoefModel.invTr_invTr _`.
-/
theorem coefPlus_is (G : GridData L sc) {θ : InfFam D} (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V (.top 0))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (G.V (.top 0)) h) = 1
      rw [show infHom (G.V (.top 0)) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h τ)
      (GlobalTheory.RecDictModel.archM_unitary (G.V (.top 0)) (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹ τ : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.FunObj.posDef_Xp G (tauE D τ)).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

end GlobalTheory.TopLineProof
