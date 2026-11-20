import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise Formalism.UG

namespace GlobalTheory.DefiniteDense

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infPt (y : UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) : UA E n :=
  ⟨infGL E n y.1, infGL_mem_UA y.1 (by
    have h : cT (starRingEnd (Cinf E)) (y.1 : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * y.1 = 1 := y.2
    rw [mul_one] at h
    exact h)⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.DefU.continuous_infGL.comp continuous_subtype_val).subtype_mk _`.
-/
theorem continuous_infPt : Continuous (infPt (E := E) (n := n)) :=
  (GlobalTheory.DefU.continuous_infGL.comp continuous_subtype_val).subtype_mk _

/- English proof (translation)
Establish `hne : ∃ z, (IsCMField.complexConj E : E →+* E) z ≠ z`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext h)`. Establish `hd` using `GlobalTheory.RealApprox.dense_unitary (GlobalTheory.CuspRep.InfType.diagInf E) (IsCMField.complexConj E : E →+* E) (starRingEnd (Cinf E)) (fun z => (pInf_complexConj z).symm) (fun z => IsCMField.complexConj_apply_apply E z) hne (fun z => star_star z) continuous_star GlobalTheory. …`.

Rewrite `hd` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a)` using `fun a => (infEq E).symm_apply_apply _`. Establish `hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))`. Establish `h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1` using `x.2`. Rewrite `h0` using `[mul_one]`.

Establish `e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) = (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E)`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hp]`. Express the relevant statement in the definitionally equal form `cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1`. Rewrite using `[e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hxe : infPt ⟨_, hM⟩ = x`. Use `Subtype.ext (ga_ext ?_ ?_)` and prove the remaining obligations. Conclude with `pInf_infGL _`. Conclude with `(pFin_infGL _).trans hx.symm`. Rewrite using `[← hxe]`.

Use `closure_mono ?_ (image_closure_subset_closure_image continuous_infPt ⟨_, hd ⟨_, hM⟩, rfl⟩)` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Take `⟨γ, hγ, hγh⟩` from `Subgroup.mem_map.1 hh`. Establish `hγ0 : cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * γ = 1` using `hγ`. Rewrite `hγ0` using `[mul_one]`.

Establish `hr : ratGL E n γ ∈ UA E n`. Establish `e : cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) = (cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E))`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, conjAd_algebraMap]`. Express the relevant statement in the definitionally equal form `cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * 1 * (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1`.

Rewrite using `[e, mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `r : UA E n` to `⟨ratGL E n γ, hr⟩`. Establish `hrU : r ∈ ratU E n` using `Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩`. Establish `hk : r⁻¹ * infPt h ∈ finU E n`. Establish `e1 : GeneralLinearGroup.map (pInf E) (ratGL E n γ) = h.1`.

Rewrite using `[← hγh]`. Conclude with `Units.ext rfl`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pInf E) ((ratGL E n γ)⁻¹ * infGL E n h.1) = 1`. Rewrite using `[map_mul, map_inv, e1, pInf_infGL, inv_mul_cancel]`. Conclude with `⟨r, hrU, r⁻¹ * infPt h, hk, mul_inv_cancel_left r _⟩`.
-/
theorem mem_closure_rat_fin (x : UA E n) (hx : x ∈ infU E n) :
    x ∈ closure ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
  have hne : ∃ z, (IsCMField.complexConj E : E →+* E) z ≠ z := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hd := GlobalTheory.RealApprox.dense_unitary (GlobalTheory.CuspRep.InfType.diagInf E) (IsCMField.complexConj E : E →+* E)
    (starRingEnd (Cinf E)) (fun z => (pInf_complexConj z).symm) (fun z => IsCMField.complexConj_apply_apply E z) hne
    (fun z => star_star z) continuous_star GlobalTheory.CuspRep.InfType.denseRange_diagInf Units.isOpen
    (fun z hz => by obtain ⟨u, rfl⟩ := hz; exact NormedRing.inverse_continuousAt u)
    (1 : Matrix (Fin n) (Fin n) E)
    (by rw [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]) (by simp)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at hd
  have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) := fun a => (infEq E).symm_apply_apply _
  have hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
    have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
    rw [mul_one] at h0
    have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
        (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
      ext i j
      simp [Formalism.UG.cT, hp]
    change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
      (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
    rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hxe : infPt ⟨_, hM⟩ = x := by
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans hx.symm
  rw [← hxe]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPt ⟨_, hd ⟨_, hM⟩, rfl⟩)
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 hh
  have hγ0 : cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * γ = 1 := hγ
  rw [mul_one] at hγ0
  have hr : ratGL E n γ ∈ UA E n := by
    have e : cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
        (cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
      ext i j
      simp [Formalism.UG.cT, conjAd_algebraMap]
    change cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * 1 *
      (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1
    rw [e, mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]
  let r : UA E n := ⟨ratGL E n γ, hr⟩
  have hrU : r ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩
  have hk : r⁻¹ * infPt h ∈ finU E n := by
    have e1 : GeneralLinearGroup.map (pInf E) (ratGL E n γ) = h.1 := by
      rw [← hγh]
      exact Units.ext rfl
    change GeneralLinearGroup.map (pInf E) ((ratGL E n γ)⁻¹ * infGL E n h.1) = 1
    rw [map_mul, map_inv, e1, pInf_infGL, inv_mul_cancel]
  exact ⟨r, hrU, r⁻¹ * infPt h, hk, mul_inv_cancel_left r _⟩

/- English proof (translation)
Introduce `L _ _ _ n φ hφ h0`. Establish `hS : ((ratU L n : Set (UA L n)) * (finU L n : Set (UA L n))) ⊆ {g | φ g = 0}`. Introduce and unpack `_ ⟨γ, hγ, k, hk, rfl⟩`. Express the relevant statement in the definitionally equal form `φ (γ * k) = 0`. Rewrite using `[hφ.left γ hγ k]`.

Conclude with `h0 k hk`. Establish `hZ : IsClosed {g : UA L n | φ g = 0}` using `isClosed_eq hφ.cont continuous_const`. Use function extensionality and compare the values at `g`. Take `⟨k, hk, x, hx, rfl⟩` from `GlobalTheory.DefU.exists_finU_mul_infU L n g`. Rewrite using `[GlobalTheory.DefU.fin_mul_inf hk hx]`.

Establish `hc : Continuous (· * k : UA L n → UA L n)` using `continuous_mul_const k`. Establish `hxk : x * k ∈ closure ((ratU L n : Set (UA L n)) * (finU L n : Set (UA L n)))`. Use `closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, mem_closure_rat_fin x hx, rfl⟩)` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩`. Conclude with `⟨γ, hγ, k' * k, (finU L n).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩`.

Conclude with `hZ.closure_subset_iff.2 hS hxk`.
-/
theorem eq_zero_of_finU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ),
    IsAutFormU φ → (∀ y ∈ finU L n, φ y = 0) → φ = 0 := by
  intro L _ _ _ n φ hφ h0
  have hS : ((ratU L n : Set (UA L n)) * (finU L n : Set (UA L n))) ⊆ {g | φ g = 0} := by
    rintro _ ⟨γ, hγ, k, hk, rfl⟩
    change φ (γ * k) = 0
    rw [hφ.left γ hγ k]
    exact h0 k hk
  have hZ : IsClosed {g : UA L n | φ g = 0} := isClosed_eq hφ.cont continuous_const
  funext g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU L n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA L n → UA L n) := continuous_mul_const k
  have hxk : x * k ∈ closure ((ratU L n : Set (UA L n)) * (finU L n : Set (UA L n))) := by
    refine closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, mem_closure_rat_fin x hx, rfl⟩)
    rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
    exact ⟨γ, hγ, k' * k, (finU L n).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩
  exact hZ.closure_subset_iff.2 hS hxk

end GlobalTheory.DefiniteDense
