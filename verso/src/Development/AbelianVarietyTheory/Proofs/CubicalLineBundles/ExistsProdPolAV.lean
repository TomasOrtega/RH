import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PolProd

open GlobalTheory.CechPic GlobalTheory.TripleProd

variable {S : Scheme.{0}}

/- English proof (translation)
Establish `h` using `H.sub ((locZero_base π 0).sub H')`. Rewrite `h` using `[map_zero, zero_sub, sub_neg_eq_add]`. Then use the resulting hypothesis.
-/
theorem locZero_add {Y B : Scheme.{0}} {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) :
    LocZero π (c + d) := by
  have h := H.sub ((locZero_base π 0).sub H')
  rwa [map_zero, zero_sub, sub_neg_eq_add] at h

/- English proof (translation)
Conclude with `(cls_eq_zero_iff (pull_isLB hL _)).symm`.
-/
theorem rigidified_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 := by
  exact (cls_eq_zero_iff (pull_isLB hL _)).symm

/- English proof (translation)
Use `forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_` and prove the remaining obligations. Use `(cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_` and prove the remaining obligations. Establish `e : cls (LB.LinComb L (K` using `Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]) (LB.isLB_linComb hL _ _) = pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by`. Use `(cls_linComb hL _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Use `show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) + (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = _`. Rewrite using `[one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]`. Rewrite using `[e]`.
-/
theorem sym_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Sym A L ↔ LocZero A.hom (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
  refine forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_
  have e : cls (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]) (LB.isLB_linComb hL _ _) =
      pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
    refine (cls_linComb hL _ _ _).trans ?_
    rw [Fin.sum_univ_two]
    show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
      (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = _
    rw [one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]
  rw [e]

/- English proof (translation)
Establish `h : η[A] ≫ f = η[G]` using `IsMonHom.one_hom f`. Conclude with `congrArg (fun z => z.left) h`.
-/
theorem eSec_comp {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    eSec A ≫ f.left = eSec G := by
  have h : η[A] ≫ f = η[G] := IsMonHom.one_hom f
  exact congrArg (fun z => z.left) h

/- English proof (translation)
Establish `h : (GrpObj.inv : A ⟶ A) ≫ f = f ≫ GrpObj.inv` using `GrpObj.inv_hom f`. Conclude with `congrArg (fun z => z.left) h`.
-/
theorem inv_comp_left {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : G ⟶ G).left := by
  have h : (GrpObj.inv : A ⟶ A) ≫ f = f ≫ GrpObj.inv := GrpObj.inv_hom f
  exact congrArg (fun z => z.left) h

/- English proof (translation)
Introduce `_ R _ _ P P'`. Establish `hB : IsAbelianScheme (P.A ⊗ P'.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb`. Set `p` to `fst P.A P'.A`. Set `q` to `snd P.A P'.A`. Take `⟨M, hM, eM⟩` from `cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))`.

Establish `hd` using `LB.isLB_div hM (pull_isLB P.isLB p.left)`. Establish `last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left)`. Use `(cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]`. Use `haveI := P.isAb.proper`.

Use `haveI := P'.isAb.proper`. Use `haveI := hB.proper`. Establish `hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom` using `by haveI := P.smoothDim haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip P'.smoothDim`. Rewrite using `[add_comm]`. Conclude with `inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))`.

Establish `hrig : Out.Rigidified (P.A ⊗ P'.A) M`. Rewrite using `[rigidified_iff _ hM, eM, map_add, ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q, (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]`. Establish `hsym : Out.Sym (P.A ⊗ P'.A) M`. Establish `h₁` using `((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)`. Establish `h₂` using `((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)`.

Rewrite using `[sym_iff _ hM, eM]`. Use `locZero_add h₁ h₂ using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p, inv_comp_left q]`. Normalize the expressions using the abelian group laws. Establish `hamp : Out.RelAmple (P.A ⊗ P'.A) M` using `(relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample) ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample) hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm …`.

Use `⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, hamp, kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, inferInstance, inferInstance, ?_, rfl⟩` and prove the remaining obligations. Use `show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))`. Rewrite using `[lift_fst_snd]`. Use `infer_instance`.
-/
theorem exists_prod_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  intro _ R _ _ P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  obtain ⟨M, hM, eM⟩ := cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))
  have hd := LB.isLB_div hM (pull_isLB P.isLB p.left)
  have last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left) := by
    refine (cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_
    rw [cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Out.Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add, ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  have hamp : Out.RelAmple (P.A ⊗ P'.A) M :=
    (relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box
      ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample) ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample)
      hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm)
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, hamp,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, inferInstance, inferInstance, ?_, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.PolProd
