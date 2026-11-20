import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableExtendByZeroOffSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFunctionalIterPartialDerivStatement
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolFunc

variable {d : ℕ}

def extLin {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) : S →ₗ[ℂ] (E d → ℂ) where
  toFun u := ext0 U ((u : U →ᵇ ℂ) : U → ℂ)
  map_add' u v := by funext x; exact GlobalTheory.HCA.SolSub.matrixExtendByZero_add (u : U →ᵇ ℂ) v x
  map_smul' c u := by funext x; exact GlobalTheory.HCA.SolSub.extendByZeroOffSubset_smul_apply c (u : U →ᵇ ℂ) x

/- English proof (translation)
Distinguish the cases in `hx : x ∈ U`. Establish `: (fun u : S => extLin S u x) = fun u : S => (u : U →ᵇ ℂ) ⟨x, hx⟩`. Use function extensionality and compare the values at `u`. Simplify using `[extLin, ext0, hx]`. Rewrite using `[this]`.

Conclude with `(BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtype_val`. Establish `: (fun u : S => extLin S u x) = fun _ => 0`. Use function extensionality and compare the values at `u`. Simplify using `[extLin, ext0, hx]`. Rewrite using `[this]`.

Conclude with `continuous_const`.
-/
theorem continuous_extLin_apply {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) (x : E d) :
    Continuous fun u : S => extLin S u x := by
  by_cases hx : x ∈ U
  · have : (fun u : S => extLin S u x) = fun u : S => (u : U →ᵇ ℂ) ⟨x, hx⟩ := by
      funext u; simp [extLin, ext0, hx]
    rw [this]
    exact (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtype_val
  · have : (fun u : S => extLin S u x) = fun _ => 0 := by
      funext u; simp [extLin, ext0, hx]
    rw [this]; exact continuous_const

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `: U.domRestrict (ext0 U u) = u` using `by funext x; exact dif_pos x.2`. Rewrite using `[this]`. Conclude with `u.continuous`.
-/
theorem continuousOn_extendByZeroOffSubset {U : Set (E d)} (u : U →ᵇ ℂ) : ContinuousOn (ext0 U u) U := by
  rw [continuousOn_iff_continuous_restrict]
  have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
  rw [this]; exact u.continuous

end GlobalTheory.HCA.SolFunc

open GlobalTheory.HCA.SolFunc in

/- English proof (translation)
Introduce `d ι _ P U hU ha hell S hS w x hx`. Establish `hcl : IsClosed (S : Set (U →ᵇ ℂ))`. Rewrite using `[hS]`. Conclude with `(GlobalTheory.HCA.solSet_closed_submodule d ι P U hU ha).1`. Use `haveI : CompleteSpace S := hcl.completeSpace_coe`.

Establish `hsm : ∀ u : S, ContDiffOn ℝ ∞ (extLin S u) U`. Introduce `u`. Establish `hu : (u : U →ᵇ ℂ) ∈ solSet P U` using `by rw [← hS]; exact u.2`. Conclude with `ZetaZeros.D.EllReg.elliptic_regularity_of_parts d ι P U _ ⟨hU, ha, hell, continuousOn_extendByZeroOffSubset _, hu⟩`. Take `⟨l, hl⟩` from `GlobalTheory.T.exists_continuous_functional_iterPartialDeriv d U hU S (extLin S) (fun y _ => continuous_extLin_apply S y) hsm w x hx`.

Conclude with `⟨l, fun u => hl u⟩`.
-/
theorem GlobalTheory.HCA.dw_solSet_continuous_functional : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  intro d ι _ P U hU ha hell S hS w x hx
  have hcl : IsClosed (S : Set (U →ᵇ ℂ)) := by
    rw [hS]; exact (GlobalTheory.HCA.solSet_closed_submodule d ι P U hU ha).1
  haveI : CompleteSpace S := hcl.completeSpace_coe
  have hsm : ∀ u : S, ContDiffOn ℝ ∞ (extLin S u) U := by
    intro u
    have hu : (u : U →ᵇ ℂ) ∈ solSet P U := by rw [← hS]; exact u.2
    exact ZetaZeros.D.EllReg.elliptic_regularity_of_parts d ι P U _ ⟨hU, ha, hell, continuousOn_extendByZeroOffSubset _, hu⟩
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_continuous_functional_iterPartialDeriv d U hU S (extLin S) (fun y _ => continuous_extLin_apply S y) hsm w x hx
  exact ⟨l, fun u => hl u⟩
