import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ _ _ ε T f`. Take `⟨a, b, hb0, hfab⟩` from `T.io_surj f`. Establish `hiob : T.io b ≠ 0`. Introduce `h`. Conclude with `hb0 (T.io_inj (by rw [h, map_zero]))`.

Establish `hexb : T.exp (T.io b) ≠ 0`. Introduce `h`. Conclude with `hiob (T.exp.toRingHom.injective (by simpa using h))`. Establish `hexpf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹`. Rewrite using `[← hfab, map_mul, mul_assoc, mul_inv_cancel₀ hexb, mul_one]`.

Take `⟨hops, -, -, -, hinv⟩` from `GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε`. Establish `hEa` using `T.exp_io a`. Establish `hEb` using `T.exp_io b`. Establish `hEbi` using `hinv _ _ hexb hEb`. Establish `hE : IsExp ε ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹) (T.exp f)`.

Rewrite using `[hexpf]`. Conclude with `(hops _ _ _ _ hEa hEbi).2.2`. Take `⟨hden, C, hC⟩` from `hE`. Use `⟨hden, up ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹), C, ?_, hC⟩` and prove the remaining obligations. Take `⟨⟨A, hA⟩, hmd, -, -, hHs⟩` from `GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict`.

Take `⟨-, hid, hunit⟩` from `GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units`. Establish `hbR : InR ε.range (b : ℍ → ℂ)` using `((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 b.2`. Establish `hbhol : DifferentiableOn ℂ (up (b : ℍ → ℂ)) Hs` using `(hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ hbR)`. Establish `hgb0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) ≠ 0`. Introduce `h`.

Apply `hb0` to reduce the goal to its premises. Establish `h0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero)` using `h`. Use `hid _ _ hbhol (differentiableOn_const 0) h0` as an intermediate fact. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`.

Establish `h1` using `this τ (hHs τ)`. Simplify `h1` using `[up, UpperHalfPlane.ofComplex_apply]`. Establish `hev` using `(hunit _ hbhol hgb0).1`. Establish `hgi : germ ((b : ℍ → ℂ)⁻¹) * germ (b : ℍ → ℂ) = 1`. Unfold `germ`.

Rewrite using `[← Filter.Germ.coe_mul]`. Use `show ((up ((b : ℍ → ℂ)⁻¹) * up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (1 : ℂ) : ℂ → ℂ) : Mero)`. Rewrite using `[Filter.Germ.coe_eq]`. Use `filter_upwards [hev] with z hz`. Simplify using `only [Pi.mul_apply, up, Pi.inv_apply] at hz ⊢`.

Conclude with `inv_mul_cancel₀ hz`. Establish `hanf : T.an f * germ (b : ℍ → ℂ) = germ (a : ℍ → ℂ)`. Rewrite using `[← T.an_io, ← T.an_io, ← map_mul, hfab]`. Use `show T.an f = germ ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹)`. Rewrite using `[← hA, map_mul, hA, hA, ← hanf, mul_assoc, mul_comm (germ (b : ℍ → ℂ)), hgi, mul_one]`.
-/
theorem frac_exp_converges : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (f : T.K), Den (T.exp f) ∧ ∃ (φ : ℂ → ℂ) (C : ℝ), T.an f = (φ : Mero) ∧ HS ε C φ (T.exp f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb0, hfab⟩ := T.io_surj f
  have hiob : T.io b ≠ 0 := by
    intro h
    exact hb0 (T.io_inj (by rw [h, map_zero]))
  have hexb : T.exp (T.io b) ≠ 0 := by
    intro h
    exact hiob (T.exp.toRingHom.injective (by simpa using h))
  have hexpf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hfab, map_mul, mul_assoc, mul_inv_cancel₀ hexb, mul_one]
  obtain ⟨hops, -, -, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hEa := T.exp_io a
  have hEb := T.exp_io b
  have hEbi := hinv _ _ hexb hEb
  have hE : IsExp ε ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹) (T.exp f) := by
    rw [hexpf]; exact (hops _ _ _ _ hEa hEbi).2.2
  obtain ⟨hden, C, hC⟩ := hE
  refine ⟨hden, up ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹), C, ?_, hC⟩

  obtain ⟨⟨A, hA⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  have hbR : InR ε.range (b : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 b.2
  have hbhol : DifferentiableOn ℂ (up (b : ℍ → ℂ)) Hs := (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ hbR)
  have hgb0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) ≠ 0 := by
    intro h
    apply hb0
    have h0 : ((up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h
    have := hid _ _ hbhol (differentiableOn_const 0) h0
    apply Subtype.ext
    funext τ
    have h1 := this τ (hHs τ)
    simpa [up, UpperHalfPlane.ofComplex_apply] using h1
  have hev := (hunit _ hbhol hgb0).1
  have hgi : germ ((b : ℍ → ℂ)⁻¹) * germ (b : ℍ → ℂ) = 1 := by
    unfold germ
    rw [← Filter.Germ.coe_mul]
    show ((up ((b : ℍ → ℂ)⁻¹) * up (b : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((fun _ => (1 : ℂ) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_eq]
    filter_upwards [hev] with z hz
    simp only [Pi.mul_apply, up, Pi.inv_apply] at hz ⊢
    exact inv_mul_cancel₀ hz
  have hanf : T.an f * germ (b : ℍ → ℂ) = germ (a : ℍ → ℂ) := by
    rw [← T.an_io, ← T.an_io, ← map_mul, hfab]
  show T.an f = germ ((a : ℍ → ℂ) * (b : ℍ → ℂ)⁻¹)
  rw [← hA, map_mul, hA, hA, ← hanf, mul_assoc, mul_comm (germ (b : ℍ → ℂ)), hgi, mul_one]

end GlobalTheory.FN
