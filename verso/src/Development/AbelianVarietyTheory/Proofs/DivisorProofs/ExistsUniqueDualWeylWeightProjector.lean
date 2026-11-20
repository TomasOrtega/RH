import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.UG

namespace GlobalTheory.ExpFrame

def rowProj (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (w : Fin N → ℕ) :
    dualWeyl O N N ν →ₗ[O] dualWeyl O N N ν :=
  (weightedHomogeneousComponent (rowW N N) w).restrict
    (fun x hx => dualWeylModuleRowGraded O N N ν w x hx)

/- English proof (translation)
Introduce `O _ N ι _ _ lam τ w`. Establish `hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w))`. Introduce `x y hy`. Unfold `atFactor`. Rewrite using `[PiTensorProduct.map_tprod]`.

Use `congr 1`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `only [Function.update_self, LinearMap.restrict_apply, rowProj]`.

Conclude with `Subtype.ext hy.symm`. Simplify using `[Function.update_of_ne h]`. Use `⟨_, hP, fun a' ha' => ?_⟩` and prove the remaining obligations. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Simplify using `only [LinearMap.compMultilinearMap_apply]`. Set `y : dualWeyl O N N (res N (lam τ))` to `rowProj O N (res N (lam τ)) w (x τ)`. Conclude with `(ha' x y rfl).trans (hP x y rfl).symm`.
-/
theorem exists_unique_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  intro O _ N ι _ _ lam τ w
  have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
    intro x y hy
    unfold atFactor
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
      exact Subtype.ext hy.symm
    · simp [Function.update_of_ne h]
  refine ⟨_, hP, fun a' ha' => ?_⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  exact (ha' x y rfl).trans (hP x y rfl).symm

end GlobalTheory.ExpFrame

end
