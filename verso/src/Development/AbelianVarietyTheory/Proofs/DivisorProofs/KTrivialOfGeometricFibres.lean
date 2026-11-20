import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.KTrivFibres

open GlobalTheory.KTrivSpread GlobalTheory.UU

/- English proof (translation)
Introduce `T a ha x hx`. Establish `hL'` using `pull_isLB hL φ`. Establish `hxw : x.left ≫ A.hom = (a ≫ g) ≫ f` using `(Over.w x).trans (ha.symm.trans (Category.assoc _ _ _).symm)`. Set `x' : Over.mk (a ≫ g) ⟶ A'` to `Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)`. Set `U : Over.mk ((Over.mk (a ≫ g)).hom ≫ f) ⟶ T` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans (ha.symm.trans (Category.assoc _ _ _).symm))`.

Establish `e₁ : pushPt h.1.w x' = U ≫ x` using `Over.OverMorphism.ext ((h.1.lift_fst _ _ _).trans (Category.id_comp _).symm)`. Establish `e₂ : x' = 1` using `hK (Over.mk (a ≫ g)) a rfl x' (inK_of_push h hL hL' (PolBaseChange.lbIso_refl hL') x' (e₁ ▸ hx.comp U))`. Establish `e₃ : U ≫ x = U ≫ (1 : T ⟶ A)`. Rewrite using `[← e₁, MonObj.comp_one]`. Conclude with `(congrArg (pushHom h _) e₂).trans (map_one (pushHom h _))`.

Conclude with `Over.OverMorphism.ext ((Category.id_comp _).symm.trans ((congrArg (fun q => q.left) e₃).trans (Category.id_comp _)))`.
-/
theorem trivAlong_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} {L : LB A.left} (h : IsGrpPullback A' A f φ) (hL : L.IsLB) {Z : Scheme.{0}}
    {g : Z ⟶ S'} (hK : TrivAlong A' (L.pull φ) g) : TrivAlong A L (g ≫ f) := by
  intro T a ha x hx
  have hL' := pull_isLB hL φ
  have hxw : x.left ≫ A.hom = (a ≫ g) ≫ f := (Over.w x).trans (ha.symm.trans (Category.assoc _ _ _).symm)
  let x' : Over.mk (a ≫ g) ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  let U : Over.mk ((Over.mk (a ≫ g)).hom ≫ f) ⟶ T :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (ha.symm.trans (Category.assoc _ _ _).symm))
  have e₁ : pushPt h.1.w x' = U ≫ x :=
    Over.OverMorphism.ext ((h.1.lift_fst _ _ _).trans (Category.id_comp _).symm)
  have e₂ : x' = 1 := hK (Over.mk (a ≫ g)) a rfl x'
    (inK_of_push h hL hL' (PolBaseChange.lbIso_refl hL') x' (e₁ ▸ hx.comp U))
  have e₃ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [← e₁, MonObj.comp_one]
    exact (congrArg (pushHom h _) e₂).trans (map_one (pushHom h _))
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
    ((congrArg (fun q => q.left) e₃).trans (Category.id_comp _)))

/- English proof (translation)
Introduce `S _ A _ hA L hL ha hK`. Establish `hG` using `(GlobalTheory.abelianSchemeLaws_all.1).globalFns`. Use `kTriv_iff_forall.2 fun T x hx => Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun τ => ?_)` and prove the remaining obligations. Take `⟨R, j, _, ⟨p, hp⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := T.hom τ) (U := ⊤) trivial`. Establish `: IsNoetherianRing R` using `isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)`.

Set `P : PrimeSpectrum R` to `p`. Establish `: P.asIdeal.IsPrime` using `P.isPrime`. Set `F` to `AlgebraicClosure P.asIdeal.ResidueField`. Set `ψ : R →+* F` to `(algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)`. Set `j' : Sp R ⟶ S` to `j`.

Establish `: IsOpenImmersion j'` using `inferInstanceAs (IsOpenImmersion j)`. Establish `h1 : TrivAlong A L (spMap ψ ≫ j')` using `trivAlong_of_kTriv (isGrpPullback_pullback A _) hL (hK F _)`. Establish `hp'` using `isGrpPullback_pullback A j'`. Establish `hN` using `pull_isLB hL (pullback.fst A.hom j')`. Establish `hB : IsAbelianScheme ((Over.pullback j').obj A)` using `Out.TLinPf.isAb_pullback j' A hA`.

Establish `haB` using `relAmple_chart j' (𝟙 _) hL ha`. Rewrite `haB` using `[Category.id_comp j']`. Establish `h2` using `TrivAlong.pull hp' hL h1`. Establish `h3` using `kTriv_iff_forall.2 fun T' y hy => TrivAlong.pull (isGrpPullback_pullback _ (spMap ψ)) hN (g := 𝟙 _) (by rwa [Category.id_comp]) T' T'.hom (Category.comp_id _) y hy`. Take `⟨f, hf, h4⟩` from `kTriv_away_of_kTriv_fibre hG R _ _ F ψ hB hN haB h3`.

Establish `h6` using `trivAlong_push hp' hL (trivAlong_of_kTriv (isGrpPullback_pullback _ _) hN h4)`. Establish `hfp : f ∉ P.asIdeal` using `fun hm => hf (by show algebraMap _ F (algebraMap R P.asIdeal.ResidueField f) = 0`. Rewrite using `[(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero])`. Establish `hτ : T.hom τ ∈ Set.range (spMap (algebraMap R (Localization.Away f)) ≫ j')`. Establish `hq : P ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))`.

Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]`. Conclude with `hfp`. Take `⟨q, hq⟩` from `hq`. Conclude with `⟨q, (congrArg j'.base hq).trans hp⟩`. Set `W` to `T.hom ⁻¹ᵁ (spMap (algebraMap R (Localization.Away f)) ≫ j').opensRange`.

Set `u : Over.mk (W.ι ≫ T.hom) ⟶ T` to `Over.homMk W.ι rfl`. Establish `hr : Set.range (W.ι ≫ T.hom) ⊆ Set.range (spMap (algebraMap R (Localization.Away f)) ≫ j')`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `y.2`. Establish `e` using `h6 (Over.mk (W.ι ≫ T.hom)) (IsOpenImmersion.lift _ _ hr) (IsOpenImmersion.lift_fac _ _ _) _ (hx.comp u)`.

Conclude with `⟨W, hτ, congrArg (fun q => q.left) (e.trans (MonObj.comp_one u).symm)⟩`.
-/
theorem kTriv_of_geometricFibres : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → Out.RelAmple A M → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.KTriv ((Over.pullback y).obj A) (M.pull (pullback.fst A.hom y))) → Out.KTriv A M := by
  intro S _ A _ hA L hL ha hK
  have hG := (GlobalTheory.abelianSchemeLaws_all.1).globalFns
  refine kTriv_iff_forall.2 fun T x hx => Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun τ => ?_)
  obtain ⟨R, j, _, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := T.hom τ) (U := ⊤) trivial
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)
  let P : PrimeSpectrum R := p
  have : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  let j' : Sp R ⟶ S := j
  have : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion j)
  have h1 : TrivAlong A L (spMap ψ ≫ j') := trivAlong_of_kTriv (isGrpPullback_pullback A _) hL (hK F _)
  have hp' := isGrpPullback_pullback A j'
  have hN := pull_isLB hL (pullback.fst A.hom j')
  have hB : IsAbelianScheme ((Over.pullback j').obj A) := Out.TLinPf.isAb_pullback j' A hA
  have haB := relAmple_chart j' (𝟙 _) hL ha
  rw [Category.id_comp j'] at haB
  have h2 := TrivAlong.pull hp' hL h1
  have h3 := kTriv_iff_forall.2 fun T' y hy =>
    TrivAlong.pull (isGrpPullback_pullback _ (spMap ψ)) hN (g := 𝟙 _) (by rwa [Category.id_comp]) T' T'.hom
      (Category.comp_id _) y hy
  obtain ⟨f, hf, h4⟩ := kTriv_away_of_kTriv_fibre hG R _ _ F ψ hB hN haB h3
  have h6 := trivAlong_push hp' hL (trivAlong_of_kTriv (isGrpPullback_pullback _ _) hN h4)
  have hfp : f ∉ P.asIdeal := fun hm => hf (by
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField f) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero])
  have hτ : T.hom τ ∈ Set.range (spMap (algebraMap R (Localization.Away f)) ≫ j') := by
    have hq : P ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact hfp
    obtain ⟨q, hq⟩ := hq
    exact ⟨q, (congrArg j'.base hq).trans hp⟩
  let W := T.hom ⁻¹ᵁ (spMap (algebraMap R (Localization.Away f)) ≫ j').opensRange
  let u : Over.mk (W.ι ≫ T.hom) ⟶ T := Over.homMk W.ι rfl
  have hr : Set.range (W.ι ≫ T.hom) ⊆ Set.range (spMap (algebraMap R (Localization.Away f)) ≫ j') := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  have e := h6 (Over.mk (W.ι ≫ T.hom)) (IsOpenImmersion.lift _ _ hr) (IsOpenImmersion.lift_fac _ _ _) _ (hx.comp u)
  exact ⟨W, hτ, congrArg (fun q => q.left) (e.trans (MonObj.comp_one u).symm)⟩

end GlobalTheory.KTrivFibres
