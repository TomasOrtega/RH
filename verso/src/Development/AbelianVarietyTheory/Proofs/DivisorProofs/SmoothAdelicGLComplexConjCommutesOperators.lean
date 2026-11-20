import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section
namespace GlobalTheory.SmoothConj
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [chart, Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  simp only [chart, Function.comp_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a)` using `φ.2`. Use `show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)`. Introduce `g`. Rewrite using `[chart_conj]`. Conclude with `Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)`.
-/
theorem conj_mem (φ : Sm E a) : (fun x => starRingEnd ℂ (φ.1 x)) ∈ Sm E a := by
  have hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a) := φ.2
  show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)
  intro g
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

def conjMap (φ : Sm E a) : Sm E a := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem φ⟩

def conjEquiv : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun := conjMap
  invFun := conjMap
  map_add' x y := by apply Subtype.ext; funext g; simp [conjMap]
  map_smul' c x := by apply Subtype.ext; funext g; simp [conjMap]
  left_inv x := by apply Subtype.ext; funext g; simp [conjMap]
  right_inv x := by apply Subtype.ext; funext g; simp [conjMap]

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => rfl`. Consider the case `cpt k => rfl`. Consider the case `lie X`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Use `show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)`. Simplify using `only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]`. Both sides reduce to the same expression.
-/
theorem conjEquiv_act (o : Op E a) (φ : Sm E a) :
    act o (conjEquiv φ) = conjEquiv (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    apply Subtype.ext; funext g
    show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)
    simp only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

end GlobalTheory.SmoothConj

namespace GlobalTheory
open GlobalTheory.CuspRep

/- English proof (translation)
Introduce `_ _ _ _ _` and use `⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩`.
-/
theorem smooth_conj_commutes_act : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧
      ∀ o φ, act o (C φ) = C (act o φ) :=
  fun _ _ _ _ _ => ⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩

end GlobalTheory
