import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMapStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[star_mul']`.
-/
theorem star_comp_const_smul_eq_conj_smul {α : Type*} (a : ℂ) (F : α → ℂ) :
    (fun x => star ((a • F) x)) = (starRingEnd ℂ a) • (fun x => star (F x)) := by
  funext x
  simp [star_mul']

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj`. Establish `hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1`. Introduce `τ`. Take `⟨c, -, hc⟩` from `hConj`. Establish `h1` using `(X.low (X.pl.symm τ)).1`.

Rewrite using `[← (c τ).norm_map, hc τ]`. Conclude with `h1`. Establish `hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0` using `fun τ h0 => by`. Use `hnorm τ` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `hfun` using `GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hCusp D X h θ S M J χ t hθ hMat`. Take `⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀))` from `⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩`. Establish `hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X` using `fun T => GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)`. Establish `hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)` using `fun T => by filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2`.

Rewrite using `[h1, Pi.star_apply, h2]`. Establish `e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) = (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) + (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x))`. Introduce `T T'`. Rewrite using `[Submodule.coe_add, LinearMap.add_apply]`. Use function extensionality and compare the values at `x`.

Conclude with `star_add _ _`. Establish `e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) = (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x))`. Introduce `a T`. Rewrite using `[Submodule.coe_smul, LinearMap.smul_apply]`. Generalize the expression as in `T.1 (PiTensorProduct.tprod ℂ v₀) = F`.

Conclude with `star_comp_const_smul_eq_conj_smul a (evS X h t F)`. Set `j : MultT θ M J χ →ₗ⋆[ℂ] HHX X` to `{ toFun := fun T => ⟨star (f T), hmem T⟩ map_add' := fun T T' => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show star (f (T + T')) = star (f T) + star (f T')`. Apply `Lp.ext` to reduce the goal to its premises.

Use `(hstar (T + T')).trans ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm`. Use the proof step `map_smul' := fun a T => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Submodule.coe_smul]`. Apply `Lp.ext` to reduce the goal to its premises. Use `(hstar (a • T)).trans ?_` and prove the remaining obligations. Rewrite using `[e2]`. Conclude with `((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }`.

Establish `hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)` using `hstar`. Use `⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `T hT`. Establish `h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0`.

Rewrite using `[hT]`. Conclude with `Lp.coeFn_zero _ _ _`. Establish `hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0` using `by filter_upwards [hj T, h0] with x h1 h2`. Rewrite `h1` using `[h2]`. Establish `h3` using `congrArg star h1`.

Rewrite `h3` using `[star_star]`. Rewrite using `[← h3]`. Conclude with `star_zero _`. Conclude with `Subtype.ext (GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)`. Introduce `ψ`.

Establish `hψ : star (star (ψ : L2X X)) ∈ HHX X` using `by rw [star_star]; exact ψ.2`. Take `⟨T, hT, hTe⟩` from `GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj (star (ψ : L2X X)) hψ`. Use `⟨⟨T, hT⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Lp.ext` to reduce the goal to its premises.

Use `(hj ⟨T, hT⟩).trans ?_` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3`. Rewrite `h3` using `[h2, Pi.star_apply]`. Rewrite using `[← h3, star_star]`.
-/
theorem evalAll_rows : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  intro hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
  have hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨c, -, hc⟩ := hConj
    have h1 := (X.low (X.pl.symm τ)).1
    rw [← (c τ).norm_map, hc τ]
    exact h1
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hfun := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hCusp D X h θ S M J χ t hθ hMat
  obtain ⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) :=
    ⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩
  have hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X := fun T =>
    GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)
  have hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := fun T => by
    filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2
    rw [h1, Pi.star_apply, h2]
  have e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) +
        (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro T T'
    rw [Submodule.coe_add, LinearMap.add_apply]
    funext x
    exact star_add _ _
  have e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro a T
    rw [Submodule.coe_smul, LinearMap.smul_apply]
    generalize T.1 (PiTensorProduct.tprod ℂ v₀) = F
    exact star_comp_const_smul_eq_conj_smul a (evS X h t F)
  let j : MultT θ M J χ →ₗ⋆[ℂ] HHX X :=
    { toFun := fun T => ⟨star (f T), hmem T⟩
      map_add' := fun T T' => by
        apply Subtype.ext
        show star (f (T + T')) = star (f T) + star (f T')
        apply Lp.ext
        refine (hstar (T + T')).trans ?_
        rw [e1]
        exact ((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun a T => by
        apply Subtype.ext
        rw [Submodule.coe_smul]
        apply Lp.ext
        refine (hstar (a • T)).trans ?_
        rw [e2]
        exact ((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }
  have hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := hstar
  refine ⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩
  · rw [injective_iff_map_eq_zero]
    intro T hT
    have h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0 := by
      rw [hT]; exact Lp.coeFn_zero _ _ _
    have hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 := by
      filter_upwards [hj T, h0] with x h1 h2
      rw [h2] at h1
      have h3 := congrArg star h1
      rw [star_star] at h3
      rw [← h3]
      exact star_zero _
    exact Subtype.ext (GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)
  · intro ψ
    have hψ : star (star (ψ : L2X X)) ∈ HHX X := by rw [star_star]; exact ψ.2
    obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
      (star (ψ : L2X X)) hψ
    refine ⟨⟨T, hT⟩, ?_⟩
    apply Subtype.ext
    apply Lp.ext
    refine (hj ⟨T, hT⟩).trans ?_
    filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3
    rw [h2, Pi.star_apply] at h3
    rw [← h3, star_star]

end GlobalTheory.Core.Mi
