import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `E _ _ _ a U hU ζ hζ hcen hrat hsc`. Use `choose c hc using hsc`. Take `⟨φ₀, h₀, hne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot`. Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (funext h)`. Establish `hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀` using `fun z => by`. Use `congrFun (hc z φ₀ h₀) g₀` as an intermediate fact. Rewrite `this` using `[GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis.

Establish `hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀` using `fun z => by`. Rewrite using `[hval z, mul_div_cancel_right₀ _ hg₀]`. Establish `hcont : Continuous c`. Establish `h1 : Continuous fun z => φ₀ (g₀ * ζ z)` using `(hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)`. Establish `h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀` using `funext hcz`.

Rewrite using `[h2]`. Conclude with `h1.div_const _`. Establish `hone : c 1 = 1`. Rewrite using `[hcz, map_one, mul_one, div_self hg₀]`. Establish `hmul : ∀ z z', c (z * z') = c z * c z'` using `fun z z' => by`.

Establish `h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]`. Rewrite `h1` using `[hc _ φ₀ h₀]`. Conclude with `smul_left_injective ℂ hne h1`. Set `f : Ideles E →* ℂ` to `{ toFun := c, map_one' := hone, map_mul' := hmul }`.

Establish `hinvc : Continuous fun z => (c z)⁻¹`. Use `hcont.inv₀ fun z => ?_` and prove the remaining obligations. Introduce `h0`. Use `hmul z z⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hone, h0, zero_mul]`.

Conclude with `one_ne_zero this`. Use `⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩` and prove the remaining obligations. Use `Units.continuous_iff.2 ⟨hcont, ?_⟩` and prove the remaining obligations. Establish `: (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹`. Use function extensionality and compare the values at `z`.

Rewrite using `[Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression. Conclude with `this ▸ hinvc`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c (diagUnits E k) = 1`.

Rewrite using `[hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]`. Conclude with `hc z φ hφ`.
-/
theorem UpperTheory.Gal.Int.Div.charOfZeta_of :
    CharOfZeta := by
  intro E _ _ _ a U hU ζ hζ hcen hrat hsc
  choose c hc using hsc
  obtain ⟨φ₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀ := fun z => by
    have := congrFun (hc z φ₀ h₀) g₀
    rwa [GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul] at this
  have hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀ := fun z => by
    rw [hval z, mul_div_cancel_right₀ _ hg₀]
  have hcont : Continuous c := by
    have h1 : Continuous fun z => φ₀ (g₀ * ζ z) :=
      (hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)
    have h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀ := funext hcz
    rw [h2]
    exact h1.div_const _
  have hone : c 1 = 1 := by
    rw [hcz, map_one, mul_one, div_self hg₀]
  have hmul : ∀ z z', c (z * z') = c z * c z' := fun z z' => by
    have h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀ := by
      rw [map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]
    rw [hc _ φ₀ h₀] at h1
    exact smul_left_injective ℂ hne h1
  let f : Ideles E →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  have hinvc : Continuous fun z => (c z)⁻¹ := by
    refine hcont.inv₀ fun z => ?_
    intro h0
    have := hmul z z⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩
  · refine Units.continuous_iff.2 ⟨hcont, ?_⟩
    have : (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    exact this ▸ hinvc
  · refine Units.ext ?_
    change c (diagUnits E k) = 1
    rw [hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]
  · exact hc z φ hφ
