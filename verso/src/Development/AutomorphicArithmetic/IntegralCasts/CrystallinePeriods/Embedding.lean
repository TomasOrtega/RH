import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Section
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]

namespace BdRPlus

def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)

variable {p O}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaC_apply (x : BdRPlus p O) :
    thetaC p O x = IsUnitBall.awayEquiv O p (theta p O x) := rfl

/- English proof (translation)
Rewrite using `[thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap, AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]`.
-/
@[simp] theorem thetaC_algebraMap (x : Ainf p O) :
    thetaC p O (algebraMap _ _ x) = (Ainf.theta p O x : C) := by
  rw [thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap,
    AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, RingHom.mem_ker, thetaC_apply, map_eq_zero_iff _ (IsUnitBall.awayEquiv O p).injective]`.
-/
theorem ker_thetaC : RingHom.ker (thetaC p O) = RingHom.ker (theta p O) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, thetaC_apply,
    map_eq_zero_iff _ (IsUnitBall.awayEquiv O p).injective]

/- English proof (translation)
Introduce `c`. Take `⟨x, hx⟩` from `AinfInv.theta_surjective_of_frobenius p (IsUnitBall.frobenius_surjective O p) ((IsUnitBall.awayEquiv O p).symm c)`. Conclude with `⟨algebraMap _ _ x, by rw [thetaC_apply, theta_algebraMap, hx, AlgEquiv.apply_symm_apply]⟩`.
-/
theorem thetaC_surjective [IsAlgClosed C] : Function.Surjective (thetaC p O) := by
  intro c
  obtain ⟨x, hx⟩ := AinfInv.theta_surjective_of_frobenius p (IsUnitBall.frobenius_surjective O p)
    ((IsUnitBall.awayEquiv O p).symm c)
  exact ⟨algebraMap _ _ x, by rw [thetaC_apply, theta_algebraMap, hx, AlgEquiv.apply_symm_apply]⟩

/- English proof (translation)
The claim follows from `haveI := formallyEtale_of_isAlgebraic F L hom_ext_of_formallyUnramified hF fun x => (IsUnitBall.awayEquiv O p).injective (hθ x)`.
-/
theorem hom_ext_thetaC {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
    [Algebra.IsAlgebraic F L] {s₁ s₂ : L →+* BdRPlus p O}
    (hF : ∀ a : F, s₁ (algebraMap F L a) = s₂ (algebraMap F L a))
    (hθ : ∀ x, thetaC p O (s₁ x) = thetaC p O (s₂ x)) : s₁ = s₂ :=
  haveI := formallyEtale_of_isAlgebraic F L
  hom_ext_of_formallyUnramified hF fun x => (IsUnitBall.awayEquiv O p).injective (hθ x)

variable [IsAlgClosed C]

section General

variable {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
  [Algebra.IsAlgebraic F L]

def sectionC (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) :
    L →+* BdRPlus p O :=
  haveI := formallyEtale_of_isAlgebraic F L
  «section» (AinfInv.theta_surjective_of_frobenius p (IsUnitBall.frobenius_surjective O p)) ι
    ((IsUnitBall.awayEquiv O p).symm.toRingEquiv.toRingHom.comp j) (fun a => by
      change (IsUnitBall.awayEquiv O p).symm (j _) = _
      rw [AlgEquiv.symm_apply_eq, hj]
      rfl)

/- English proof (translation)
Use `haveI := formallyEtale_of_isAlgebraic F L`. Rewrite using `[thetaC_apply, sectionC, theta_section]`. Conclude with `(IsUnitBall.awayEquiv O p).apply_symm_apply _`.
-/
@[simp] theorem thetaC_sectionC (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) (x : L) :
    thetaC p O (sectionC ι j hj x) = j x := by
  haveI := formallyEtale_of_isAlgebraic F L
  rw [thetaC_apply, sectionC, theta_section]
  exact (IsUnitBall.awayEquiv O p).apply_symm_apply _

/- English proof (translation)
Use `haveI := formallyEtale_of_isAlgebraic F L`. Rewrite using `[sectionC, section_algebraMap]`.
-/
@[simp] theorem sectionC_algebraMap (ι : F →+* AinfInv p O) (j : L →+* C)
    (hj : ∀ a : F, j (algebraMap F L a) = thetaC p O (algebraMap _ _ (ι a))) (a : F) :
    sectionC ι j hj (algebraMap F L a) = algebraMap _ _ (ι a) := by
  haveI := formallyEtale_of_isAlgebraic F L
  rw [sectionC, section_algebraMap]

end General

end BdRPlus

section Padic

variable [NormedAlgebra ℚ_[p] C]

omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] in

def IsUnitBall.ofPadicInt : ℤ_[p] →+* O :=
  ((algebraMap ℚ_[p] C).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict _ fun x =>
    (IsUnitBall.mem_iff _).2 (by
      rw [RingHom.comp_apply, norm_algebraMap']; exact x.norm_le_one)

variable {p O} in

/- English proof (translation)
Use `AinfInv.theta_algebraMap_padic (IsUnitBall.ofPadicInt p O) ((IsUnitBall.awayEquiv O p).symm.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] C)) (fun a => by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(IsUnitBall.awayEquiv O p).symm _ = _`. Rewrite using `[AlgEquiv.symm_apply_eq, IsUnitBall.awayEquiv_algebraMap]`. Use the proof step `rfl) a`. Rewrite using `[BdRPlus.thetaC_apply, IsScalarTower.algebraMap_apply ℚ_[p] (AinfInv p O), BdRPlus.theta_algebraMap, this]`.

Conclude with `(IsUnitBall.awayEquiv O p).apply_symm_apply _`.
-/
@[simp] theorem BdRPlus.thetaC_algebraMap_padic (a : ℚ_[p]) :
    BdRPlus.thetaC p O (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] C a := by
  have := AinfInv.theta_algebraMap_padic (IsUnitBall.ofPadicInt p O)
    ((IsUnitBall.awayEquiv O p).symm.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] C))
    (fun a => by
      change (IsUnitBall.awayEquiv O p).symm _ = _
      rw [AlgEquiv.symm_apply_eq, IsUnitBall.awayEquiv_algebraMap]
      rfl) a
  rw [BdRPlus.thetaC_apply, IsScalarTower.algebraMap_apply ℚ_[p] (AinfInv p O),
    BdRPlus.theta_algebraMap, this]
  exact (IsUnitBall.awayEquiv O p).apply_symm_apply _

variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]

def BdRPlus.padicSection (j : L →ₐ[ℚ_[p]] C) : L →ₐ[ℚ_[p]] BdRPlus p O :=
  { BdRPlus.sectionC (algebraMap ℚ_[p] (AinfInv p O)) (j : L →+* C) (fun a => by
      rw [← IsScalarTower.algebraMap_apply, BdRPlus.thetaC_algebraMap_padic]
      exact j.commutes a) with
    commutes' := fun a => BdRPlus.sectionC_algebraMap _ _ _ a }

variable {p O}

/- English proof (translation)
Use `BdRPlus.thetaC_sectionC (algebraMap ℚ_[p] (AinfInv p O)) (j : L →+* C) (fun a => ?_) x` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, BdRPlus.thetaC_algebraMap_padic]`. Conclude with `j.commutes a`.
-/
@[simp] theorem BdRPlus.thetaC_padicSection (j : L →ₐ[ℚ_[p]] C) (x : L) :
    BdRPlus.thetaC p O (BdRPlus.padicSection p O j x) = j x := by
  refine BdRPlus.thetaC_sectionC (algebraMap ℚ_[p] (AinfInv p O)) (j : L →+* C) (fun a => ?_) x
  rw [← IsScalarTower.algebraMap_apply, BdRPlus.thetaC_algebraMap_padic]
  exact j.commutes a

/- English proof (translation)
The claim follows from `AlgHom.coe_ringHom_injective (BdRPlus.hom_ext_thetaC (F := ℚ_[p]) (fun a => (s.commutes a).trans ((BdRPlus.padicSection p O j).commutes a).symm) (fun x => (h x).trans (BdRPlus.thetaC_padicSection j x).symm))`.
-/
theorem BdRPlus.eq_padicSection (j : L →ₐ[ℚ_[p]] C) (s : L →ₐ[ℚ_[p]] BdRPlus p O)
    (h : ∀ x, BdRPlus.thetaC p O (s x) = j x) : s = BdRPlus.padicSection p O j :=
  AlgHom.coe_ringHom_injective (BdRPlus.hom_ext_thetaC (F := ℚ_[p])
    (fun a => (s.commutes a).trans ((BdRPlus.padicSection p O j).commutes a).symm)
    (fun x => (h x).trans (BdRPlus.thetaC_padicSection j x).symm))

end Padic

section Witt

variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]

omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] [IsUnitBall O] [IsAlgClosed C] in
/- English proof (translation)
Use `⟨fun m n h => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom)` using `(WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective`. Conclude with `Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))`.
-/
theorem charZero_wittVector : CharZero (WittVector p k) := by
  refine ⟨fun m n h => ?_⟩
  have hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))

instance : CharZero (FractionRing (WittVector p k)) :=
  haveI := charZero_wittVector p (k := k)
  inferInstance

variable {p O}

/- English proof (translation)
The claim follows from `RingHom.congr_fun (fracWitt_hom_ext (f := j.comp (algebraMap _ L)) (g := (BdRPlus.thetaC p O).comp ((algebraMap _ _).comp (AinfInv.liftFracWitt p g))) (fun a => by simp only [RingHom.comp_apply] rw [hj, BdRPlus.thetaC_apply, BdRPlus.theta_algebraMap, AinfInv.theta_liftFracWitt, I …`.
-/
theorem BdRPlus.thetaC_liftFracWitt (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a)
    (a : FractionRing (WittVector p k)) :
    j (algebraMap _ L a) = BdRPlus.thetaC p O (algebraMap _ _ (AinfInv.liftFracWitt p g a)) :=
  RingHom.congr_fun (fracWitt_hom_ext (f := j.comp (algebraMap _ L))
    (g := (BdRPlus.thetaC p O).comp ((algebraMap _ _).comp (AinfInv.liftFracWitt p g)))
    (fun a => by
      simp only [RingHom.comp_apply]
      rw [hj, BdRPlus.thetaC_apply, BdRPlus.theta_algebraMap, AinfInv.theta_liftFracWitt,
        IsUnitBall.awayEquiv_algebraMap])) a

def BdRPlus.wittSection (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a) :
    L →+* BdRPlus p O :=
  BdRPlus.sectionC (AinfInv.liftFracWitt p g) j (BdRPlus.thetaC_liftFracWitt g j hj)

/- English proof (translation)
The claim follows from `BdRPlus.thetaC_sectionC _ _ _ x`.
-/
@[simp] theorem BdRPlus.thetaC_wittSection (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a) (x : L) :
    BdRPlus.thetaC p O (BdRPlus.wittSection g j hj x) = j x :=
  BdRPlus.thetaC_sectionC _ _ _ x

/- English proof (translation)
The claim follows from `BdRPlus.sectionC_algebraMap _ _ _ a`.
-/
theorem BdRPlus.wittSection_algebraMap (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a)
    (a : FractionRing (WittVector p k)) :
    BdRPlus.wittSection g j hj (algebraMap _ L a) = algebraMap _ _ (AinfInv.liftFracWitt p g a) :=
  BdRPlus.sectionC_algebraMap _ _ _ a

end Witt

def padicAlgClToBdRPlus : PadicAlgCl p →ₐ[ℚ_[p]] BdRPlus p (PadicComplexInt p) :=
  BdRPlus.padicSection p (PadicComplexInt p) (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])

/- English proof (translation)
The claim follows from `BdRPlus.thetaC_padicSection _ x`.
-/
@[simp] theorem thetaC_padicAlgClToBdRPlus (x : PadicAlgCl p) :
    BdRPlus.thetaC p (PadicComplexInt p) (padicAlgClToBdRPlus p x) = (x : ℂ_[p]) :=
  BdRPlus.thetaC_padicSection _ x

end Reformulated.AutPerF
