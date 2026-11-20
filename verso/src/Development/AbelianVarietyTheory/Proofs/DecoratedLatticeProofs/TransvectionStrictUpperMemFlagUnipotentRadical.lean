import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvFlag

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

/- English proof (translation)
Establish `h1 : (fun i => cA D (vecX d b i)) = (d.jX.map (cA D)) *ᵥ (fun i => cA D (b i))`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (cA D) d.jX b i`. Rewrite using `[form, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, d.pY_eq, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem form_vecX {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (b : Fin ρ → AE D) (y : VA V) :
    form V y (vecX d b) = (fun i => cA D (b i)) ⬝ᵥ (d.pY *ᵥ y) := by
  have h1 : (fun i => cA D (vecX d b i)) = (d.jX.map (cA D)) *ᵥ (fun i => cA D (b i)) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.jX b i
  rw [form, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, d.pY_eq, ← Matrix.mulVec_mulVec]
  rfl

/- English proof (translation)
Use `Matrix.ext_of_mulVec_single fun k => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one T k, h k]`. Both sides reduce to the same expression.
-/
theorem mul_eq_of_cols {R : Type} [CommRing R] {n ρ : ℕ} (M : Matrix (Fin n) (Fin n) R) (E : Matrix (Fin n) (Fin ρ) R)
    (T : Matrix (Fin ρ) (Fin ρ) R)
    (h : ∀ k, M *ᵥ (E *ᵥ Pi.single k 1) = E *ᵥ Pi.single k 1 + E *ᵥ (fun i => T i k)) : M * E = E + E * T := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one T k, h k]
  rfl

/- English proof (translation)
Introduce `D V V₀ ρ d b v hb u hu`. Unfold `flagN`. Rewrite using `[GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]`. Establish `hperp : ∀ y : VA V, d.pY *ᵥ y = 0 → act V u y = y + d.jX *ᵥ (form V y v • b)`. Introduce `y hy`.

Rewrite using `[hu y, transv, form_vecX, hy, dotProduct_zero, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero, Matrix.mulVec_smul]`. Both sides reduce to the same expression. Use `⟨⟨Matrix.of fun i k => form V (vecX d (Pi.single k 1)) v * b i, fun j i hij => hb j i hij, ?_⟩, fun y hy => ⟨form V y v • b, hperp y hy⟩⟩` and prove the remaining obligations. Establish `e1 : d.e.map (incA D) = d.jX` using `rfl`. Rewrite using `[e1]`.

Use `mul_eq_of_cols _ _ _ fun k => ?_` and prove the remaining obligations. Establish `hk : d.pY *ᵥ vecX d (Pi.single k 1) = 0`. Rewrite using `[vecX, Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]`. Conclude with `hperp _ hk`.
-/
theorem transv_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (b : Fin ρ → AE D)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V),
    (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * b i = 0) →
    ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d b) v u → u ∈ flagN d := by
  intro D V V₀ ρ d b v hb u hu
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  have hperp : ∀ y : VA V, d.pY *ᵥ y = 0 → act V u y = y + d.jX *ᵥ (form V y v • b) := by
    intro y hy
    rw [hu y, transv, form_vecX, hy, dotProduct_zero, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero,
      Matrix.mulVec_smul]
    rfl
  refine ⟨⟨Matrix.of fun i k => form V (vecX d (Pi.single k 1)) v * b i, fun j i hij => hb j i hij, ?_⟩,
    fun y hy => ⟨form V y v • b, hperp y hy⟩⟩
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1]
  refine mul_eq_of_cols _ _ _ fun k => ?_
  have hk : d.pY *ᵥ vecX d (Pi.single k 1) = 0 := by
    rw [vecX, Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]
  exact hperp _ hk

end GlobalTheory.TransvFlag
