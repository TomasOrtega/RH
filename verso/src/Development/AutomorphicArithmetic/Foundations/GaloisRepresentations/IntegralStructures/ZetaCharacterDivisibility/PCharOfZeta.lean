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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
