import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
/- English proof (translation)
Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hτ : ι.toRingHom.comp (ι.symm.toRingHom.comp τ0) = τ0` using `by ext x; simp`. Use `set τ : E →+* Qbar l := ι.symm.toRingHom.comp τ0 with hτdef`. Use `set X : Multiset ℂ := (HT τ).map (fun n : ℤ => (n : ℂ)) with hXdef`. Establish `hX : X = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + (-1) * z)`.

Rewrite using `[hXdef, H.weights τ, hτ, hinf, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) = X.map (fun z => (wt : ℂ) + (-1) * z)`.

Rewrite using `[H.weights_conj, hXdef, Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hZ : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + 1 * z)`. Rewrite using `[H.weights, comp_complexConj, hτ, hinf, hconj, Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcX : (X.card : ℂ) = a` using `by rw [hX, Multiset.card_map, hcard]`. Establish `e` using `congrArg Multiset.sum (hY.symm.trans hZ)`. Rewrite `e` using `[sum_map_affine, sum_map_affine, hcX, hX, sum_map_affine, hcard]`. Establish `ha0 : (a : ℂ) ≠ 0` using `by exact_mod_cast (by omega : a ≠ 0)`. Establish `h : (wt : ℂ) = (a : ℂ) - 1 - 2 * (s : ℂ)`.

Apply `mul_left_cancel₀ ha0` to reduce the goal to its premises. Take the linear combination `e`. Conclude with `h` after adjusting the coercions.
-/
theorem weight_eq_alt_alt {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {χ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (m : (E →+* ℂ) → Multiset ℂ) (s : ℝ)
    (hcard : ∀ τ, (m τ).card = a) (hinf : ∀ τ, (CG.mk π).infChar τ = (m τ).map (· + (s : ℂ)))
    (hconj : ∀ τ, m (ComplexEmbedding.conjugate τ) = (m τ).map Neg.neg) :
    (wt : ℝ) = (a : ℝ) - 1 - 2 * s := by
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ι.toRingHom.comp (ι.symm.toRingHom.comp τ0) = τ0 := by ext x; simp
  set τ : E →+* Qbar l := ι.symm.toRingHom.comp τ0 with hτdef
  set X : Multiset ℂ := (HT τ).map (fun n : ℤ => (n : ℂ)) with hXdef
  have hX : X = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + (-1) * z) := by
    rw [hXdef, H.weights τ, hτ, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hY : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      X.map (fun z => (wt : ℂ) + (-1) * z) := by
    rw [H.weights_conj, hXdef, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]; push_cast; ring
  have hZ : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + 1 * z) := by
    rw [H.weights, comp_complexConj, hτ, hinf, hconj, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hcX : (X.card : ℂ) = a := by rw [hX, Multiset.card_map, hcard]
  have e := congrArg Multiset.sum (hY.symm.trans hZ)
  rw [sum_map_affine, sum_map_affine, hcX, hX, sum_map_affine, hcard] at e
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h : (wt : ℂ) = (a : ℂ) - 1 - 2 * (s : ℂ) := by
    apply mul_left_cancel₀ ha0
    linear_combination e
  exact_mod_cast h
end GlobalTheory.TempSatGal
end
end
end
