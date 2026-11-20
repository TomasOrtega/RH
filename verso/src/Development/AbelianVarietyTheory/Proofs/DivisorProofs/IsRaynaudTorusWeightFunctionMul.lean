import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtMul

open GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

/- English proof (translation)
Establish `hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ')` using `unit_ext fun y _ => by`. Take `⟨J, hJ, -⟩` from `exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)`. Establish `e₁` using `GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'`. Establish `e₂` using `GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'`. Rewrite `e₁`, `e₂` using `[Ray.Φ_b]`.

Rewrite `e₂` using `[hq]`. Simplify using `only [GlobalTheory.TorusModel.cv] at e₁ e₂`. Rewrite `e₂` using `[hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm]`. Rewrite using `[map_mul]`. Conclude with `mul_right_cancel e₂`.

Use `congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu` as an intermediate fact. Simplify using `only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this`. Use `Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))` and prove the remaining obligations. Conclude with `congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)`.
-/
theorem c_add {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hq : x' ≫ Y.q = x ≫ Y.q)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J)
    (χ χ' : Q.X) : c (χ + χ') = c χ * c χ' := by
  have hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ') := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e₁ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'
    have e₂ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'
    rw [Ray.Φ_b] at e₁ e₂
    rw [hq] at e₂
    dsimp only [GlobalTheory.TorusModel.cv] at e₁ e₂
    rw [hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm] at e₂
    rw [map_mul]
    exact mul_right_cancel e₂
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this
  refine Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))
  exact congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc`. Rewrite using `[valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc, hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isWt_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  intro R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]
  ring

end GlobalTheory.Heat.WtMul
