import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

/- English proof (translation)
Use `set h : Fˣ → ℂ := fun a => f a * (((1 : Fˣ →* ℂˣ) a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hh`. Use `set g : E → ℂ := fun x => f (Algebra.norm F x) * ((modulus (Algebra.norm F x) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hg`. Establish `hgu : (fun x : Eˣ => g x) = h ∘ normUnits F E`. Use function extensionality and compare the values at `x`. Simplify using `[hh, hg, coe_normUnits]`.

Establish `hcont : Continuous (fun x : Eˣ => g x)`. Rewrite using `[hgu]`. Conclude with `(continuous_localZeta_integrand hf continuous_one (1 / 2)).comp (continuous_normUnits F E)`. Establish `hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → g (x * u) = g x`. Introduce `x u hu`.

Simplify using `only [hg, map_mul, hu, mul_one]`. Establish `hL : localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = ∫ x : Eˣ, g x ∂multHaar E`. Unfold `localZeta`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[hg, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E)]`.

Establish `hfib : ∀ a : Fˣ, nfib E g a = (1 / 2 : ℂ) * (h a + f a * ((η a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ))`. Introduce `a`. Distinguish the cases in `hr : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)`. Establish `e1 : nfib E g a = g (hr.choose : E)` using `dif_pos hr`. Establish `e2 : ((η a : ℂˣ) : ℂ) = 1` using `by rw [hη, nsg, if_pos hr]`.

Rewrite using `[e1, e2]`. Simplify using `only [hg, hh, hr.choose_spec]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : nfib E g a = 0` using `dif_neg hr`.

Establish `e2 : ((η a : ℂˣ) : ℂ) = -1` using `by rw [hη, nsg, if_neg hr]`. Rewrite using `[e1, e2]`. Simplify using `only [hh]`. Simplify using the standard rewrite rules. Establish `hexp1 : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0`.

Simplify using `[quasiCharExponent]`. Establish `hexpη : quasiCharExponent η = 0`. Establish `: ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[hη, nsg]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `[quasiCharExponent, this]`. Establish `hi1` using `integrable_localZeta (s := 1 / 2) hf (continuous_one : Continuous (1 : Fˣ →* ℂˣ)) (by rw [hexp1]; norm_num)`. Establish `hi2` using `integrable_localZeta (s := 1 / 2) hf hc (by rw [hexpη]; norm_num)`. Rewrite using `[hL, (hκ g hcont hinv).2, integral_congr_ae (Filter.Eventually.of_forall hfib), integral_const_mul, integral_add hi1 hi2]`. Unfold `localZeta`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localZeta_comp_norm_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
    [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ) (hc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) (κ : ℝ) (hκ : FibProp F E κ) (f : F → ℂ)
    (hf : f ∈ schwartzBruhat F) :
    localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) =
      (κ / 2 : ℂ) * (localZeta f 1 (1 / 2) + localZeta f η (1 / 2)) := by
  classical
  set h : Fˣ → ℂ := fun a => f a * (((1 : Fˣ →* ℂˣ) a : ℂˣ) : ℂ) *
    ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hh
  set g : E → ℂ := fun x => f (Algebra.norm F x) *
    ((modulus (Algebra.norm F x) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hg
  have hgu : (fun x : Eˣ => g x) = h ∘ normUnits F E := by
    funext x
    simp [hh, hg, coe_normUnits]
  have hcont : Continuous (fun x : Eˣ => g x) := by
    rw [hgu]
    exact (continuous_localZeta_integrand hf continuous_one (1 / 2)).comp
      (continuous_normUnits F E)
  have hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → g (x * u) = g x := by
    intro x u hu
    simp only [hg, map_mul, hu, mul_one]
  have hL : localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = ∫ x : Eˣ, g x ∂multHaar E := by
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hg, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E)]
  have hfib : ∀ a : Fˣ, nfib E g a =
      (1 / 2 : ℂ) * (h a + f a * ((η a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    intro a
    by_cases hr : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)
    · have e1 : nfib E g a = g (hr.choose : E) := dif_pos hr
      have e2 : ((η a : ℂˣ) : ℂ) = 1 := by rw [hη, nsg, if_pos hr]
      rw [e1, e2]
      simp only [hg, hh, hr.choose_spec]
      simp
      ring
    · have e1 : nfib E g a = 0 := dif_neg hr
      have e2 : ((η a : ℂˣ) : ℂ) = -1 := by rw [hη, nsg, if_neg hr]
      rw [e1, e2]
      simp only [hh]
      simp
  have hexp1 : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0 := by
    simp [quasiCharExponent]
  have hexpη : quasiCharExponent η = 0 := by
    have : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := by
      rw [hη, nsg]
      split_ifs <;> simp
    simp [quasiCharExponent, this]
  have hi1 := integrable_localZeta (s := 1 / 2) hf (continuous_one : Continuous (1 : Fˣ →* ℂˣ))
    (by rw [hexp1]; norm_num)
  have hi2 := integrable_localZeta (s := 1 / 2) hf hc (by rw [hexpη]; norm_num)
  rw [hL, (hκ g hcont hinv).2, integral_congr_ae (Filter.Eventually.of_forall hfib),
    integral_const_mul, integral_add hi1 hi2]
  unfold localZeta
  push_cast
  ring

end GlobalTheory.CompanionTheory.GaussLam
