import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuOfLocallyUnitTimesPower
import Development.EtaleCohomology.KummerTheory.FinAlgExt
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitKummerEqOfPicardTorsionFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootOfKummerClassEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicRigid

/- English proof (translation)
Establish `hdeg : (Polynomial.cyclotomic q L).degree ≠ 0`. Rewrite using `[Polynomial.degree_cyclotomic]`. Use `Nat.totient_pos.mpr (NeZero.pos q)` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root _ hdeg`.

Use `⟨⟨z, hq, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hz`.
-/
private lemma exists_prim (q : ℕ) [NeZero q] (L : Type) [Field L] [IsAlgClosed L] (hq : IsUnit (q : L)) :
    Nonempty (Prim q L) := by
  have hdeg : (Polynomial.cyclotomic q L).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

/- English proof (translation)
Use `show pull (ZMod q) (sch.map (𝟙 X)) (tw q i) m y = y`. Rewrite using `[CategoryTheory.Functor.map_id, pull_id]`.
-/
private lemma pl_id (q : ℕ) (i : ℤ) {X : Scheme.{0}} (m : ℤ) (y : Ht q (sch.obj X) m i) :
    pl q i (𝟙 X) m y = y := by
  show pull (ZMod q) (sch.map (𝟙 X)) (tw q i) m y = y
  rw [CategoryTheory.Functor.map_id, pull_id]

/- English proof (translation)
Introduce `hy q _ k L _ _ _ _ _ hq C _ c hc X _ u x pb hnorm φ hφ F hF`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩` from `hy`. Establish `hP : IsProper c` using `hc.2.1`. Establish `hS1 : SmoothOfRelativeDimension 1 c` using `hc.2.2`. Establish `hS : Smooth c` using `SmoothOfRelativeDimension.smooth 1 c`.

Establish `hqL : IsUnit (q : L)` using `by simpa using hq.map (algebraMap k L)`. Establish `hxP : IsProper x` using `MorphismProperty.of_isPullback (P := @IsProper) pb hP`. Establish `hcpt : CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace x`. Set `ρ : L →+* Γ(X, ⊤)` to `((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop).hom`. Establish `hqX : IsUnit (q : Γ(X, ⊤))` using `by simpa using hqL.map ρ`.

Take `⟨ζ⟩` from `exists_prim q L hqL`. Take `⟨xx, hxx⟩` from `UpperTheory.exists_h1Mu_of_locally_unit_times_power q X ⟨Prim.map ρ ζ⟩ hqX hcpt hnorm F hF`. Establish `E` using `hA e2 e3 q k L (algebraMap k L) hq c 1`. Take `⟨x₀, hx₀⟩` from `(E 1).2 (pl q 1 pb.isoPullback.inv 1 xx)`. Establish `hu : pl q 1 u 1 x₀ = xx`.

Rewrite using `[← pb.isoPullback_hom_fst, pl_comp]`. Establish `h1 : pl q 1 (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) 1 x₀ = pl q 1 pb.isoPullback.inv 1 xx` using `hx₀`. Rewrite using `[h1, ← pl_comp, Iso.hom_inv_id, pl_id]`. Set `gC` to `C.fromSpecStalk (genericPoint C)`. Set `hk : k →+* C.functionField` to `(Spec.preimage (gC ≫ c)).hom`.

Establish `hqA : IsUnit (q : C.functionField)` using `by simpa using hq.map hk`. Establish `hqK : IsUnit (q : X.functionField)`. Simplify using `using hqA.map φ`. Establish `hqS : IsUnit (q : Γ(Spec C.functionField, ⊤))`. Simplify using `using hqA.map (Scheme.ΓSpecIso C.functionField).inv.hom`.

Establish `hqT : IsUnit (q : Γ(Spec X.functionField, ⊤))`. Simplify using `using hqK.map (Scheme.ΓSpecIso X.functionField).inv.hom`. Take `⟨w, hw⟩` from `UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree q C.functionField hqA (fun c _ => Subsingleton.elim _ _) (pl q 1 gC 1 x₀)`. Establish `K1` using `(GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (Spec.map (CommRingCat.ofHom φ)) w hqS`. Establish `K2 : kum q (X` using `Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) = kum q (Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w) := by`.

Rewrite using `[← hxx, ← hu, ← pl_comp, ← hφ, pl_comp]`. Establish `h2 : pl q 1 (C.fromSpecStalk (genericPoint C)) 1 x₀ = kum q w` using `hw.symm`. Rewrite using `[h2]`. Conclude with `K1`. Set `iX : (X.functionField)ˣ →* (Γ(Spec X.functionField, ⊤))ˣ` to `Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom`.

Set `fK : (C.functionField)ˣ` to `Units.map (Scheme.ΓSpecIso C.functionField).hom.hom.toMonoidHom w`. Set `φu : (X.functionField)ˣ` to `Units.map φ.toMonoidHom fK`. Establish `K3 : Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w = iX φu`. Apply `Units.ext` to reduce the goal to its premises. Establish `e : (Scheme.ΓSpecIso C.functionField).inv.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))) = (w : Γ(Spec C.functionField, ⊤))` using `congrArg (fun m => m.hom (w : Γ(Spec C.functionField, ⊤))) (Scheme.ΓSpecIso C.functionField).hom_inv_id`.

Establish `h3 : (Scheme.ΓSpecIso X.functionField).inv.hom (φ ((fK : (C.functionField)ˣ) : C.functionField)) = (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso C.functionField).inv.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))))` using `congrArg (fun m => m.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤)))) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))`. Rewrite `h3` using `[e]`. Conclude with `h3.symm`. Establish `K4 : kum q (iX (F * φu⁻¹)) = 0`. Establish `h4` using `((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (iX (F * φu⁻¹)) (iX φu) hqT).1`.

Rewrite `h4` using `[← map_mul, inv_mul_cancel_right]`. Establish `h5 : kum q (iX F) = kum q (iX φu)` using `K2.trans (by rw [K3])`. Rewrite `h4` using `[h5]`. Conclude with `right_eq_add.mp h4`. Take `⟨v, hv⟩` from `UpperTheory.exists_root_of_kummer_class_eq_zero q (Spec X.functionField) (iX (F * φu⁻¹)) hqT K4`.

Set `h : (X.functionField)ˣ` to `Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom v`. Establish `hh : h ^ q = F * φu⁻¹`. Establish `e1 : h ^ q = Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom (v ^ q)` using `(map_pow _ v q).symm`. Rewrite using `[e1, hv]`. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `congrArg (fun m => m.hom (((F * φu⁻¹ : (X.functionField)ˣ)) : X.functionField)) (Scheme.ΓSpecIso X.functionField).inv_hom_id`. Use `⟨fK, h, ?_⟩` and prove the remaining obligations. Establish `h6 : F = φu * h ^ q` using `by rw [hh, mul_comm F, mul_inv_cancel_left]`. Establish `h7` using `congrArg Units.val h6`. Rewrite `h7` using `[Units.val_mul, Units.val_pow_eq_pow_val]`.

Conclude with `h7`.
-/
private lemma main (hA : LateralTheory.KummerTheory.AlgExt) : Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q := by
  intro hy q _ k L _ _ _ _ _ hq C _ c hc X _ u x pb hnorm φ hφ F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩ := hy
  have hP : IsProper c := hc.2.1
  have hS1 : SmoothOfRelativeDimension 1 c := hc.2.2
  have hS : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hqL : IsUnit (q : L) := by simpa using hq.map (algebraMap k L)
  have hxP : IsProper x := MorphismProperty.of_isPullback (P := @IsProper) pb hP
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  let ρ : L →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop).hom
  have hqX : IsUnit (q : Γ(X, ⊤)) := by simpa using hqL.map ρ
  obtain ⟨ζ⟩ := exists_prim q L hqL
  obtain ⟨xx, hxx⟩ := UpperTheory.exists_h1Mu_of_locally_unit_times_power q X ⟨Prim.map ρ ζ⟩ hqX hcpt hnorm F hF
  have E := hA e2 e3 q k L (algebraMap k L) hq c 1
  obtain ⟨x₀, hx₀⟩ := (E 1).2 (pl q 1 pb.isoPullback.inv 1 xx)
  have hu : pl q 1 u 1 x₀ = xx := by
    rw [← pb.isoPullback_hom_fst, pl_comp]
    have h1 : pl q 1 (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) 1 x₀ =
      pl q 1 pb.isoPullback.inv 1 xx := hx₀
    rw [h1, ← pl_comp, Iso.hom_inv_id, pl_id]

  let gC := C.fromSpecStalk (genericPoint C)
  let hk : k →+* C.functionField := (Spec.preimage (gC ≫ c)).hom
  have hqA : IsUnit (q : C.functionField) := by simpa using hq.map hk
  have hqK : IsUnit (q : X.functionField) := by
    simpa using hqA.map φ
  have hqS : IsUnit (q : Γ(Spec C.functionField, ⊤)) := by
    simpa using hqA.map (Scheme.ΓSpecIso C.functionField).inv.hom
  have hqT : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hqK.map (Scheme.ΓSpecIso X.functionField).inv.hom
  obtain ⟨w, hw⟩ := UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree q C.functionField hqA (fun c _ => Subsingleton.elim _ _) (pl q 1 gC 1 x₀)
  have K1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (Spec.map (CommRingCat.ofHom φ)) w hqS
  have K2 : kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w) := by
    rw [← hxx, ← hu, ← pl_comp, ← hφ, pl_comp]
    have h2 : pl q 1 (C.fromSpecStalk (genericPoint C)) 1 x₀ = kum q w := hw.symm
    rw [h2]
    exact K1
  let iX : (X.functionField)ˣ →* (Γ(Spec X.functionField, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
  let fK : (C.functionField)ˣ := Units.map (Scheme.ΓSpecIso C.functionField).hom.hom.toMonoidHom w
  let φu : (X.functionField)ˣ := Units.map φ.toMonoidHom fK
  have K3 : Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w = iX φu := by
    apply Units.ext
    have e : (Scheme.ΓSpecIso C.functionField).inv.hom
        ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))) = (w : Γ(Spec C.functionField, ⊤)) :=
      congrArg (fun m => m.hom (w : Γ(Spec C.functionField, ⊤))) (Scheme.ΓSpecIso C.functionField).hom_inv_id
    have h3 : (Scheme.ΓSpecIso X.functionField).inv.hom (φ ((fK : (C.functionField)ˣ) : C.functionField)) =
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso C.functionField).inv.hom
          ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤)))) :=
      congrArg (fun m => m.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    rw [e] at h3
    exact h3.symm
  have K4 : kum q (iX (F * φu⁻¹)) = 0 := by
    have h4 := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (iX (F * φu⁻¹)) (iX φu) hqT).1
    rw [← map_mul, inv_mul_cancel_right] at h4
    have h5 : kum q (iX F) = kum q (iX φu) := K2.trans (by rw [K3])
    rw [h5] at h4
    exact right_eq_add.mp h4
  obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q (Spec X.functionField) (iX (F * φu⁻¹)) hqT K4
  let h : (X.functionField)ˣ := Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom v
  have hh : h ^ q = F * φu⁻¹ := by
    have e1 : h ^ q = Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom (v ^ q) := (map_pow _ v q).symm
    rw [e1, hv]
    apply Units.ext
    exact congrArg (fun m => m.hom (((F * φu⁻¹ : (X.functionField)ˣ)) : X.functionField))
      (Scheme.ΓSpecIso X.functionField).inv_hom_id
  refine ⟨fK, h, ?_⟩
  have h6 : F = φu * h ^ q := by rw [hh, mul_comm F, mul_inv_cancel_left]
  have h7 := congrArg Units.val h6
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at h7
  exact h7

end UpperTheory.PicRigid

/- English proof (translation)
The claim follows from `UpperTheory.PicRigid.main LateralTheory.Fin.AlgExt.intersectionNumber_baseChange`.
-/
theorem UpperTheory.baseChange_curve_functionField_comp_of_normal :
    Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q :=
  UpperTheory.PicRigid.main LateralTheory.Fin.AlgExt.intersectionNumber_baseChange
