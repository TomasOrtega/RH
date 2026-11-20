import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumPol

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.PolProd

/- English proof (translation)
Establish `Hf` using `isPullback_morphismRestrict f U`. Establish `Hg` using `isPullback_morphismRestrict g U`. Establish `Hh` using `isPullback_morphismRestrict h U`. Establish `w₁ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ p) ≫ f` using `by rw [Category.assoc, hh, Hh.w]`. Establish `w₂ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ q) ≫ g` using `by rw [Category.assoc, ← P.w, hh, Hh.w]`.

Use `⟨Hf.lift _ _ w₁, Hg.lift _ _ w₂, Hf.lift_snd _ _ _, Hg.lift_snd _ _ _, ?_⟩` and prove the remaining obligations. Establish `A : IsPullback (Hf.lift _ _ w₁) (h ⁻¹ᵁ U).ι (f ⁻¹ᵁ U).ι p`. Use `IsPullback.of_right ?_ (Hf.lift_snd _ _ _) Hf` and prove the remaining obligations. Rewrite using `[Hf.lift_fst, hh]`. Conclude with `Hh`.

Establish `B` using `A.paste_vert P`. Use `IsPullback.of_bot ?_ (by rw [Hf.lift_fst, Hg.lift_fst]) Hg` and prove the remaining obligations. Rewrite using `[Hg.lift_snd, Hf.w]`. Conclude with `B`.
-/
theorem exists_isPullback_restrict {X Y Z S : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (P : IsPullback p q f g) (h : Z ⟶ S) (hh : p ≫ f = h) (U : S.Opens) :
    ∃ (p' : (h ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme) (q' : (h ⁻¹ᵁ U).toScheme ⟶ (g ⁻¹ᵁ U).toScheme),
      p' ≫ (f ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ p ∧ q' ≫ (g ⁻¹ᵁ U).ι = (h ⁻¹ᵁ U).ι ≫ q ∧
        IsPullback p' q' (f ∣_ U) (g ∣_ U) := by
  have Hf := isPullback_morphismRestrict f U
  have Hg := isPullback_morphismRestrict g U
  have Hh := isPullback_morphismRestrict h U
  have w₁ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ p) ≫ f := by rw [Category.assoc, hh, Hh.w]
  have w₂ : (h ∣_ U) ≫ U.ι = ((h ⁻¹ᵁ U).ι ≫ q) ≫ g := by rw [Category.assoc, ← P.w, hh, Hh.w]
  refine ⟨Hf.lift _ _ w₁, Hg.lift _ _ w₂, Hf.lift_snd _ _ _, Hg.lift_snd _ _ _, ?_⟩
  have A : IsPullback (Hf.lift _ _ w₁) (h ⁻¹ᵁ U).ι (f ⁻¹ᵁ U).ι p := by
    refine IsPullback.of_right ?_ (Hf.lift_snd _ _ _) Hf
    rw [Hf.lift_fst, hh]
    exact Hh
  have B := A.paste_vert P
  refine IsPullback.of_bot ?_ (by rw [Hf.lift_fst, Hg.lift_fst]) Hg
  rw [Hg.lift_snd, Hf.w]
  exact B

/- English proof (translation)
Use `(relAmple_iff_isAmpleLB _ hN).2 fun U hU => ?_` and prove the remaining obligations. Take `⟨p', q', hp, hq, H⟩` from `exists_isPullback_restrict (p := (fst A B).left) (q := (snd A B).left) (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) (A ⊗ B).hom (Over.w _) U`. Establish `: IsAffine U` using `hU`. Establish `h₀` using `pull_isLB hN ((A ⊗ B).hom ⁻¹ᵁ U).ι`. Establish `h₁` using `pull_isLB (pull_isLB hL (A.hom ⁻¹ᵁ U).ι) p'`.

Establish `h₂` using `pull_isLB (pull_isLB hM (B.hom ⁻¹ᵁ U).ι) q'`. Use `IsAmpleLB.box ((relAmple_iff_isAmpleLB _ hL).1 aL U hU) ((relAmple_iff_isAmpleLB _ hM).1 aM U hU) h₀ H ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div h₀ h₁) h₂)).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_div (LB.isLB_div h₀ h₁) h₂, cls_div h₀ h₁, cls_pull hN, e, cls_pull (pull_isLB hL _), cls_pull hL, cls_pull (pull_isLB hM _), cls_pull hM, map_add, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, hp, hq]`. Normalize the expressions using the abelian group laws.
-/
theorem relAmple_prod {S : Scheme.{0}} (A B : Over S) [IsProper A.hom] [IsProper B.hom] [IsProper (A ⊗ B).hom]
    {L : LB A.left} {M : LB B.left} {N : LB (A ⊗ B).left} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (e : cls N hN = pull (fst A B).left (cls L hL) + pull (snd A B).left (cls M hM))
    (aL : RelAmple A L) (aM : RelAmple B M) : RelAmple (A ⊗ B) N := by
  refine (relAmple_iff_isAmpleLB _ hN).2 fun U hU => ?_
  obtain ⟨p', q', hp, hq, H⟩ := exists_isPullback_restrict (p := (fst A B).left) (q := (snd A B).left)
    (f := A.hom) (g := B.hom) (IsPullback.of_hasPullback _ _) (A ⊗ B).hom (Over.w _) U
  have : IsAffine U := hU
  have h₀ := pull_isLB hN ((A ⊗ B).hom ⁻¹ᵁ U).ι
  have h₁ := pull_isLB (pull_isLB hL (A.hom ⁻¹ᵁ U).ι) p'
  have h₂ := pull_isLB (pull_isLB hM (B.hom ⁻¹ᵁ U).ι) q'
  refine IsAmpleLB.box ((relAmple_iff_isAmpleLB _ hL).1 aL U hU) ((relAmple_iff_isAmpleLB _ hM).1 aM U hU) h₀ H
    ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div h₀ h₁) h₂)).1 ?_)
  rw [cls_div (LB.isLB_div h₀ h₁) h₂, cls_div h₀ h₁, cls_pull hN, e, cls_pull (pull_isLB hL _), cls_pull hL,
    cls_pull (pull_isLB hM _), cls_pull hM, map_add, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, hp, hq]
  abel

/- English proof (translation)
Introduce `S P P'`. Establish `hB : IsAbelianScheme (P.A ⊗ P'.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb`. Set `p` to `fst P.A P'.A`. Set `q` to `snd P.A P'.A`. Set `M : LB (P.A ⊗ P'.A).left` to `extLB P.L P'.L p.left q.left`.

Establish `hM : M.IsLB` using `isLB_tens (pull_isLB P.isLB p.left) (pull_isLB P'.isLB q.left)`. Establish `eM : cls M hM = pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB)` using `rfl`. Use `haveI := P.isAb.proper`. Use `haveI := P'.isAb.proper`. Use `haveI := hB.proper`.

Establish `hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom` using `by haveI := P.smoothDim haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip P'.smoothDim`. Rewrite using `[add_comm]`. Conclude with `inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))`. Establish `hrig : Rigidified (P.A ⊗ P'.A) M`. Rewrite using `[rigidified_iff _ hM, eM, map_add, ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q, (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]`.

Establish `hsym : Out.Sym (P.A ⊗ P'.A) M`. Establish `h₁` using `((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)`. Establish `h₂` using `((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)`. Rewrite using `[sym_iff _ hM, eM]`. Use `locZero_add h₁ h₂ using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p, inv_comp_left q]`. Normalize the expressions using the abelian group laws. Use `⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, relAmple_prod _ _ P.isLB P'.isLB hM eM P.ample P'.ample, kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, ⟨inferInstance, inferInstance, ?_, PolBaseChange.lbIso_refl hM⟩, rfl⟩` and prove the remaining obligations. Use `show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))`. Rewrite using `[lift_fst_snd]`.

Use `infer_instance`.
-/
theorem exists_sum_polAV : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  intro S P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  let M : LB (P.A ⊗ P'.A).left := extLB P.L P'.L p.left q.left
  have hM : M.IsLB := isLB_tens (pull_isLB P.isLB p.left) (pull_isLB P'.isLB q.left)
  have eM : cls M hM = pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB) := rfl
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
  have hrig : Rigidified (P.A ⊗ P'.A) M := by
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
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym,
    relAmple_prod _ _ P.isLB P'.isLB hM eM P.ample P'.ample,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q,
    ⟨inferInstance, inferInstance, ?_, PolBaseChange.lbIso_refl hM⟩, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.MumProd.SumPol
