import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `q _ D R R' _ _ _ b gb β hβ N N₀ c hN hpos _ X s o`. Substitute `hN` using the available equality. Establish `hN₀ : 0 < N₀` using `Nat.pos_of_mul_pos_right hpos`. Establish `hc : 0 < c` using `Nat.pos_of_mul_pos_left hpos`. Set `o₁` to `o.forgetMul hN₀ hc`.

Set `o₀ : Obj b N₀ (s ≫ spMap β)` to `GenCmp.toObj hβ.1 hβ.2 o₁ (GenCmp.genericObject_kernelCondition o₁)`. Take `⟨m⟩` from `RepFamModel.objMap_refl o₀`. Conclude with `⟨o₀, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩`.
-/
theorem UpperTheory.quotient_moduli_object_exists : UpperTheory.Gal.Int.Geo.QObj := by
  intro q _ D R R' _ _ _ b gb β hβ N N₀ c hN hpos _ X s o
  subst hN
  have hN₀ : 0 < N₀ := Nat.pos_of_mul_pos_right hpos
  have hc : 0 < c := Nat.pos_of_mul_pos_left hpos
  let o₁ := o.forgetMul hN₀ hc
  let o₀ : Obj b N₀ (s ≫ spMap β) := GenCmp.toObj hβ.1 hβ.2 o₁ (GenCmp.genericObject_kernelCondition o₁)
  obtain ⟨m⟩ := RepFamModel.objMap_refl o₀
  exact ⟨o₀, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩
