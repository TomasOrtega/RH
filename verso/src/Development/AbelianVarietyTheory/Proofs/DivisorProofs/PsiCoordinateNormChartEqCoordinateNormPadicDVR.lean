import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiNormCoord

open Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Unfold `valF`. Rewrite using `[dif_pos (by exact h)]`. Establish `e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j), (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R))) ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D …`. Introduce `h'`. Both sides reduce to the same expression.

Use `(congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_` and prove the remaining obligations. Establish `e2 : DegPre.toOpen (R` using `R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by`. Establish `: (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _` using `rfl`. Simplify using `only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.

Rewrite using `[e2]`. Establish `n` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))`. Establish `n'` using `congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'`. Conclude with `n'.symm`.
-/
theorem valF_eq {D : DegPre R} {χ : D.X} {r : R} (j : PUnit → D.P.L.ι)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) :
    valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  unfold valF
  rw [dif_pos (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

/- English proof (translation)
Take `⟨j₀, hj₀, h₀, e₀⟩` from `hr`. Establish `h` using `PsiCoordLocal.generic_le D χ j hj`. Take `⟨u, hu⟩` from `PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀`. Set `φ` to `RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))`. Use `⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩` and prove the remaining obligations.

Establish `k : DegPre.toOpen (R` using `R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val`. Rewrite using `[map_mul, map_mul, k, e₀]`. Conclude with `(congrArg Units.val hu).symm`.
-/
theorem exists_unit_valF {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (j : PUnit → D.P.L.ι)
    (hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    ∃ u : Rˣ, valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) (u * r) := by
  obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
  have h := PsiCoordLocal.generic_le D χ j hj
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀
  let φ := RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e₀]
  exact (congrArg Units.val hu).symm

/- English proof (translation)
Establish `h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1` using `by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]`. Use `le_antisymm (hf _) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_unit {S C : Type} [CommRing S] [NormedField C] (f : S →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Sˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

/- English proof (translation)
Introduce `p _ W _ _ _ _ hball D y`. Use `haveI : CharZero W := ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero`. Establish `hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1` using `fun a => (hball _).2 ⟨a, rfl⟩`. Use `⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Take `⟨j₀, hj₀, h₀, e₀⟩` from `hr`.

Use `h j₀ hj₀` as an intermediate fact. Rewrite `this` using `[valF_eq j₀ h₀ e₀]`. Then use the resulting hypothesis. Introduce `j hj`. Take `⟨u, hu⟩` from `exists_unit_valF hr j hj`. Rewrite using `[hu, map_mul, map_mul, norm_mul]`.

Use `norm_unit _ hf u` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this, _root_.one_mul, h]`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  intro p _ W _ _ _ _ hball D y
  haveI : CharZero W :=
    ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero
  have hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1 :=
    fun a => (hball _).2 ⟨a, rfl⟩
  refine ⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
    have := h j₀ hj₀
    rwa [valF_eq j₀ h₀ e₀] at this
  · intro j hj
    obtain ⟨u, hu⟩ := exists_unit_valF hr j hj
    rw [hu, map_mul, map_mul, norm_mul]
    have := norm_unit _ hf u
    simp only [RingHom.comp_apply] at this
    rw [this, _root_.one_mul, h]

end GlobalTheory.PsiNormCoord
