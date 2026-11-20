import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalFormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeOne

open Classical in

/- English proof (translation)
Introduce `L _ _ _ n v w Dv U hU W _ _ f hf`. Establish `hfU : ∀ κ ∈ U, ∀ g, f (g * κ) = f g` using `fun κ hκ g => congrFun (hf κ hκ) g`. Establish `key : ∀ x : GAf L n, TrivOutside {v} x → Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) (Dv.loc x) = if x ∈ U then 1 else 0`. Introduce `x hx`. Establish `hg` using `GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv x`.

Unfold `InertDatum.hval`. Rewrite using `[dif_pos hg]`. Distinguish the cases in `hxU : x ∈ U`. Rewrite using `[if_pos hxU]`. Establish `hK` using `GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv x ((hU x hx).1 hxU) hg`.

Unfold `Formalism.UG.dosetInd`. Rewrite using `[Set.indicator_of_mem]`. Both sides reduce to the same expression. Rewrite using `[DoubleCoset.mem_doubleCoset]`. Conclude with `⟨_, hK, 1, one_mem _, by simp⟩`.

Rewrite using `[if_neg hxU]`. Unfold `Formalism.UG.dosetInd`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `hmem`. Rewrite `hmem` using `[DoubleCoset.mem_doubleCoset]`.

Take `⟨a, ha, b, hb, e⟩` from `hmem`. Establish `hK : (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n`. Rewrite using `[e, mul_one]`. Conclude with `mul_mem ha hb`. Establish `hK'` using `hK`.

Simplify using `only [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hK'`. Apply `hxU` to reduce the goal to its premises. Use `(hU x hx).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv x hx ?_)` and prove the remaining obligations. Introduce `i j`. Conclude with `GlobalTheory.InertUmax.entries_mem_of_range _ _ hK'.2 i j`.

Use function extensionality and compare the values at `g`. Unfold `heckeFunI`. Establish `h1 : TrivOutside {v} (1 : GAf L n)`. Introduce `u _`. Simplify using the standard rewrite rules.

Rewrite using `[finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]`. Establish `hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x` using `⟨1, rfl, h1⟩`. Rewrite using `[dif_pos hc]`. Establish `hmem : hc.choose ∈ U`. Use `QuotientGroup.eq.1 hc.choose_spec.1.symm` as an intermediate fact.

Simplify using `using this`. Rewrite using `[key _ hc.choose_spec.2, if_pos hmem, one_smul, hfU _ hmem]`. Introduce `c hc1 split_ifs with hc`. Rewrite using `[key _ hc.choose_spec.2, if_neg, zero_smul]`. Introduce `hmem`.

Apply `hc1` to reduce the goal to its premises. Rewrite using `[← hc.choose_spec.1]`. Conclude with `QuotientGroup.eq.2 (by simpa using U.inv_mem hmem)`. Both sides reduce to the same expression.
-/
theorem heckeFunI_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  have hfU : ∀ κ ∈ U, ∀ g, f (g * κ) = f g := fun κ hκ g => congrFun (hf κ hκ) g
  have key : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) (Dv.loc x) = if x ∈ U then 1 else 0 := by
    intro x hx
    have hg := GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm L n v w Dv x
    unfold InertDatum.hval
    rw [dif_pos hg]
    by_cases hxU : x ∈ U
    · rw [if_pos hxU]
      have hK := GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer L n v w Dv x ((hU x hx).1 hxU) hg
      unfold Formalism.UG.dosetInd
      rw [Set.indicator_of_mem]
      · rfl
      · rw [DoubleCoset.mem_doubleCoset]
        exact ⟨_, hK, 1, one_mem _, by simp⟩
    · rw [if_neg hxU]
      unfold Formalism.UG.dosetInd
      apply Set.indicator_of_notMem
      intro hmem
      rw [DoubleCoset.mem_doubleCoset] at hmem
      obtain ⟨a, ha, b, hb, e⟩ := hmem
      have hK : (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
        rw [e, mul_one]; exact mul_mem ha hb
      have hK' := hK
      simp only [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hK'
      apply hxU
      refine (hU x hx).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv x hx ?_)
      intro i j
      exact GlobalTheory.InertUmax.entries_mem_of_range _ _ hK'.2 i j
  funext g
  unfold heckeFunI
  have h1 : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    simp
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x := ⟨1, rfl, h1⟩
    rw [dif_pos hc]
    have hmem : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hc.choose_spec.1.symm
      simpa using this
    rw [key _ hc.choose_spec.2, if_pos hmem, one_smul, hfU _ hmem]
  · intro c hc1
    split_ifs with hc
    · rw [key _ hc.choose_spec.2, if_neg, zero_smul]
      intro hmem
      apply hc1
      rw [← hc.choose_spec.1]
      exact QuotientGroup.eq.2 (by simpa using U.inv_mem hmem)
    · rfl

end GlobalTheory.InertHeckeOne
