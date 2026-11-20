import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNonemptyCrystallineTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperUnitaryLevelGaloisActsOnLabelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegralStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `G₁ G Y _ _ _ L₁ L K hKL hL htf lab yy₁ hsurj yy yy' h1 h2 g hg x`. Take `⟨b, hb⟩` from `hsurj (QuotientAddGroup.mk x)`. Establish `e1` using `h1 b x hb`. Establish `e2` using `h2 b x hb`. Establish `e3` using `hg (lab b) (K • x) e1`.

Rewrite `e3` using `[e2, map_nsmul]`. Rewrite `e3` using `[QuotientAddGroup.eq]`. Take `⟨w, hw⟩` from `e3`. Simplify using `only [nsmulAddMonoidHom_apply] at hw`. Establish `hK : 0 < K`.

Break down `Nat.eq_zero_or_pos K with h | h` into its components or cases. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `htf K _ hK` to reduce the goal to its premises. Rewrite using `[smul_sub, smul_add, smul_smul, hKL, hw]`. Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.UPoinc.compat_forces_congMod : ∀ (G₁ G Y : Type) [AddCommGroup G₁] [AddCommGroup G] [AddCommGroup Y] (L₁ L K : ℕ), K * L₁ = L → 0 < L → (∀ (n : ℕ) (x : Y), 0 < n → n • x = 0 → x = 0) → ∀ (lab : G₁ →+ G) (yy₁ : G₁ →+ ModN L₁ Y), Function.Surjective yy₁ → ∀ (yy yy' : G →+ ModN L Y), (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy (lab a) = QuotientAddGroup.mk (K • μ)) → (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy' (lab a) = QuotientAddGroup.mk (K • μ)) → ∀ g : Y →+ Y, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (g μ)) → ∀ x, CongMod L₁ (g x) x := by
  intro G₁ G Y _ _ _ L₁ L K hKL hL htf lab yy₁ hsurj yy yy' h1 h2 g hg x
  obtain ⟨b, hb⟩ := hsurj (QuotientAddGroup.mk x)
  have e1 := h1 b x hb
  have e2 := h2 b x hb
  have e3 := hg (lab b) (K • x) e1
  rw [e2, map_nsmul] at e3
  rw [QuotientAddGroup.eq] at e3
  obtain ⟨w, hw⟩ := e3
  simp only [nsmulAddMonoidHom_apply] at hw
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · exact h
  refine ⟨w, ?_⟩
  apply sub_eq_zero.mp
  apply htf K _ hK
  rw [smul_sub, smul_add, smul_smul, hKL, hw]
  abel
