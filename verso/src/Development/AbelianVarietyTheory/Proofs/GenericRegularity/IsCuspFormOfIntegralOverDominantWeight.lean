import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddOfMemHolSub
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspFormOfIntegralOverCuspForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory

open IntegralCusp in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hT r U hU a n N w hD hw k m cf hk hcf g hg heq`. Unfold `Formalism.L2.PjFree.cusp`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `σ hσ`.

Unfold `Formalism.L2.PjFree.holSub`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Use `show Formalism.L2.PjFree.IsHolCusp _ _ _`. Unfold `Formalism.L2.PjFree.IsHolCusp`. Introduce `j`.

Establish `hDk : Dom (k • a) (k * n)`. Unfold `Dom at hD ⊢`. Use `⟨fun τ i i' hii' => ?_, hD.2.mul_left k⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `Nat.mul_le_mul_left k (hD.1 τ hii')`.

Establish `hla : Formalism.L2.PjFree.laU (U σ) (k • a) (k * n) j = k • Formalism.L2.PjFree.laU (U σ) a n j`. Use function extensionality and compare the values at `τ i`. Rewrite using `[laU_nsmul (U σ) a n k hD.2 j τ i]`. Simplify using `[Pi.smul_apply]`. Establish `hsec` using `(hU σ hσ).2.2.2.2.1 (k • a) (k * n) hDk g hg j`.

Rewrite `hsec`, the goal using `[hla]`. Establish `hwS : ∀ s, Formalism.L2.PjFree.rdU (U σ) (w s) j ∈ ((U σ).X j).SS (Formalism.L2.PjFree.laU (U σ) a n j)`. Introduce `s`. Establish `h1` using `hw s`. Unfold `Formalism.L2.PjFree.cusp at h1`.

Establish `h2` using `h1.2`. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap] at h2`. Conclude with `GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (h2 σ hσ) j`. Use `cuspForm_of_integral_over_cuspForms E r ((U σ).X j) (Formalism.L2.PjFree.laU (U σ) a n j) N k m (fun s => Formalism.L2.PjFree.rdU (U σ) (w s) j) (fun i => MvPolynomial.map σ (cf i)) (Formalism.L2.PjFree.rdU (U σ) g j) hwS hk (fun i hi => (hcf i hi).map σ) hsec ?_` and prove the remaining obligations. Introduce `x hx`.

Establish `: _root_.IsReduced (CAt σ)` using `inferInstanceAs (_root_.IsReduced ℂ)`. Establish `hy` using `hT (CAt σ) ((U σ).un j ⟨x, hx⟩)`. Establish `key : ∀ f, Formalism.L2.PjFree.rdU (U σ) f j x = evHom ((U σ).un j ⟨x, hx⟩) hy f`. Introduce `f`. Unfold `Formalism.L2.PjFree.rdU`.

Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]`. Both sides reduce to the same expression. Simplify using `only [key]`. Establish `h3` using `congrArg (evHom ((U σ).un j ⟨x, hx⟩) hy) heq`. Simplify `h3` using `only [map_add, map_mul, map_sum, map_pow, map_zero, evHom_aeval]`.
-/
theorem cusp_of_integral_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  intro E _ _ _ H Dw l Xo c hT r U hU a n N w hD hw k m cf hk hcf g hg heq
  unfold Formalism.L2.PjFree.cusp
  refine ⟨hg, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  intro σ hσ
  unfold Formalism.L2.PjFree.holSub
  refine Submodule.subset_span ?_
  show Formalism.L2.PjFree.IsHolCusp _ _ _
  unfold Formalism.L2.PjFree.IsHolCusp
  intro j
  have hDk : Dom (k • a) (k * n) := by
    unfold Dom at hD ⊢
    refine ⟨fun τ i i' hii' => ?_, hD.2.mul_left k⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_left k (hD.1 τ hii')
  have hla : Formalism.L2.PjFree.laU (U σ) (k • a) (k * n) j = k • Formalism.L2.PjFree.laU (U σ) a n j := by
    funext τ i
    rw [laU_nsmul (U σ) a n k hD.2 j τ i]
    simp [Pi.smul_apply]
  have hsec := (hU σ hσ).2.2.2.2.1 (k • a) (k * n) hDk g hg j
  rw [hla] at hsec ⊢
  have hwS : ∀ s, Formalism.L2.PjFree.rdU (U σ) (w s) j ∈ ((U σ).X j).SS (Formalism.L2.PjFree.laU (U σ) a n j) := by
    intro s
    have h1 := hw s
    unfold Formalism.L2.PjFree.cusp at h1
    have h2 := h1.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (h2 σ hσ) j
  refine cuspForm_of_integral_over_cuspForms E r ((U σ).X j) (Formalism.L2.PjFree.laU (U σ) a n j) N k m
    (fun s => Formalism.L2.PjFree.rdU (U σ) (w s) j) (fun i => MvPolynomial.map σ (cf i))
    (Formalism.L2.PjFree.rdU (U σ) g j) hwS hk (fun i hi => (hcf i hi).map σ) hsec ?_
  intro x hx
  have : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hy := hT (CAt σ) ((U σ).un j ⟨x, hx⟩)
  have key : ∀ f, Formalism.L2.PjFree.rdU (U σ) f j x = evHom ((U σ).un j ⟨x, hx⟩) hy f := by
    intro f
    unfold Formalism.L2.PjFree.rdU
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
    rfl
  simp only [key]
  have h3 := congrArg (evHom ((U σ).un j ⟨x, hx⟩) hy) heq
  simpa only [map_add, map_mul, map_sum, map_pow, map_zero, evHom_aeval] using h3

end GlobalTheory
