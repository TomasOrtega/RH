import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff

noncomputable section

namespace GlobalTheory.FinitePartGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

/- English proof (translation)
Take `⟨h₁, -, h₃, h₄⟩` from `hR`. Use `letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra`. Establish `: IsScalarTower R (FractionRing R) F` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `ψ' : A →ₐ[R] F` to `{ ψ with commutes' := hψ }`. Establish `hi : ∀ y, IsIntegral R (ψ y)` using `fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'`.

Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := R) (M := A)`. Set `L` to `IntermediateField.adjoin (FractionRing R) (ψ '' s)`. Establish `: Finite (ψ '' s)` using `(s.finite_toSet.image ψ).to_subtype`. Establish `: FiniteDimensional (FractionRing R) L` using `IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)`. Establish `hm : ∀ y, ψ y ∈ L` using `fun y => by`.

Establish `hy : y ∈ Submodule.span R (s : Set A)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]`. Conclude with `mul_mem (L.algebraMap_mem _) hy`. Take `⟨f₁, f₂, f₃, f₄, -⟩` from `integralClosure_finite_local_of_isAdicComplete R h₄ L`.

Establish `: IsScalarTower R L F` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `j : integralClosure R L →+* F` to `(algebraMap L F).comp (algebraMap _ L)`. Establish `hj : Function.Injective j` using `Subtype.val_injective.comp Subtype.val_injective`. Set `a : A →+* integralClosure R L` to `(ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y => (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)`. Establish `ha : a.comp (algebraMap R A) = algebraMap R _` using `RingHom.ext fun r => hj (hψ r)`.

Use `⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a, ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_, fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩` and prove the remaining obligations. Rewrite using `[ha]`. Conclude with `ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance`.
-/
theorem exists_normal_factor (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (ψ : A →+* F)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap (FractionRing R) F (algebraMap R _ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (a : A →+* R'), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map (a.comp (algebraMap R A)) ≤ maximalIdeal R' ∧
      ∀ y, algebraMap (FractionRing R') F (algebraMap R' _ (a y)) = ψ y := by
  obtain ⟨h₁, -, h₃, h₄⟩ := hR
  letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ' : A →ₐ[R] F := { ψ with commutes' := hψ }
  have hi : ∀ y, IsIntegral R (ψ y) := fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let L := IntermediateField.adjoin (FractionRing R) (ψ '' s)
  have : Finite (ψ '' s) := (s.finite_toSet.image ψ).to_subtype
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)
  have hm : ∀ y, ψ y ∈ L := fun y => by
    have hy : y ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]; exact mul_mem (L.algebraMap_mem _) hy
  obtain ⟨f₁, f₂, f₃, f₄, -⟩ := integralClosure_finite_local_of_isAdicComplete R h₄ L
  have : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let j : integralClosure R L →+* F := (algebraMap L F).comp (algebraMap _ L)
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  let a : A →+* integralClosure R L := (ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)
  have ha : a.comp (algebraMap R A) = algebraMap R _ := RingHom.ext fun r => hj (hψ r)
  refine ⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a,
    ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_,
    fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩
  rw [ha]
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance

/- English proof (translation)
Establish `: IsAffine N.left` using `isAffine_of_isAffineHom N.hom`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (x ≫ N.left.isoSpec.hom)`. Establish `hf : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Rewrite `hf` using `[IsFinite.SpecMap_iff]`.

Use `letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra`. Establish `: Module.Finite R Γ(N.left, ⊤)` using `hf`. Establish `e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom (algebraMap (FractionRing R) F)` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])`. Establish `e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r)` using `fun r => congrArg (fun q => q.hom r) e`.

Take `⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩` from `exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'`. Use `⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂, fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]`.

Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))`.
-/
theorem exists_normal_point (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : Over (Sp R))
    [IsFinite N.hom] (x : Sp F ⟶ N.left) (hx : x ≫ N.hom = jFK (R := R) F ≫ jK R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (φ : R →+* R') (ξ : Sp R' ⟶ N.left), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map φ ≤ maximalIdeal R' ∧ ArcPull.Compat φ F ∧ ξ ≫ N.hom = spMap φ ∧
      (jFK (R := R') F ≫ jK R') ≫ ξ = x := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ N.left.isoSpec.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])
  have e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) e
  obtain ⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩ := exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'
  refine ⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂,
    fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))

section Transport

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

/- English proof (translation)
Introduce `e Z r y hy`. Take `⟨wL, -, he, -, HU⟩` from `(isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU`. Take `⟨k, hf, hpt, -⟩` from `HU e`. Establish `gp` using `pull_grp hD`. Take `⟨cb, cv⟩` from `(hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by`.

Rewrite using `[Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))`. Establish `hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom`. Rewrite using `[← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]`. Set `y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G')` to `Over.homMk y hy'`. Set `r' : Over.mk (r ≫ T'.hom) ⟶ T'` to `Over.homMk r rfl`.

Establish `hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left` using `gp.1.hom_ext ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm)))))) (by rw [Category.assoc, Category.assoc, Over.w, Over. …`. Use `(hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `ConstFam.exists_good' D.toPre.P.isLB z`. Establish `v` using `ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'`. Establish `eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i = ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i` using `Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i) (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)`.

Rewrite `v` using `[eP]`. Conclude with `mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))`.
-/
theorem isPointOf_thru {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}
    {g₀ : GtPt D.toPre T} {g : GtPt D'.toPre T'} (H : Thru hD.w hD.xe h g₀ g) {x₀ : T ⟶ G} {x : T' ⟶ G'}
    (hx : x.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = h ≫ x₀.left)
    (h₀ : IsPointOf U.toUnifPre g₀ x₀) : IsPointOf U'.toUnifPre g x := by
  intro e Z r y hy
  obtain ⟨wL, -, he, -, HU⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨k, hf, hpt, -⟩ := HU e
  have gp := pull_grp hD
  obtain ⟨cb, cv⟩ := (hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by
    rw [Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))
  have hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom := by
    rw [← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left := gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm))))))
    (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
  refine (hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
  have v := ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'
  have eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i =
      ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i)
      (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)
  rw [eP] at v
  exact mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))

/- English proof (translation)
Establish `m` using `FieldRestrictionTest.maps_eq hq`. Establish `m'` using `FieldRestrictionTest.maps_eq hq'`. Establish `hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i` using `fun χ i => by`. Rewrite using `[m, m', Category.id_comp]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)`.

Use `⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩` and prove the remaining obligations. Establish `a` using `(val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)`. Establish `a'` using `(val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)`. Rewrite `a`, `a'` using `[Category.id_comp]`. Use `a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))` and prove the remaining obligations.

Conclude with `Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm`.
-/
theorem isPullGtF_thru {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {T : Over (Sp R)} {T' : Over (Sp R')}
    {h : T'.left ⟶ T.left} {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru hD.w hD.xe h g₀ g) {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] {σ : Sp F ⟶ T'.left} {q : GtPtF D F}
    {q' : GtPtF D' F} (hq : GtPt.IsPullF F (σ ≫ h) g₀ q) (hq' : GtPt.IsPullF F σ g q') : IsPullGtF φ hD F q q' := by
  have m := FieldRestrictionTest.maps_eq hq
  have m' := FieldRestrictionTest.maps_eq hq'
  have hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i := fun χ i => by
    rw [m, m', Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)
  refine ⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB
    D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩
  have a := (val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
  rw [Category.id_comp] at a a'
  refine a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))
  exact Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm

end Transport

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk N g₀ x₀ hN F _ _ _ x hx q hq hg`. Establish `hL` using `firstFiveLaws`. Use `hN.finite` as an intermediate fact. Take `⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩` from `exists_normal_point R hR F N x hx`. Establish `hφ : Function.Injective φ` using `fun a b e => IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))`.

Take `⟨D', hD, A', U', hU⟩` from `UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U`. Establish `hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ` using `hξ.trans (Category.id_comp _).symm`. Take `⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T'` from `𝟙_ _) ξ g₀ gp := ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr (T' := 𝟙_ _) ξ hh g₀`. Set `x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G` to `Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh)) (pullback.lift_snd _ _ _)`. Establish `e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left` using `pullback.lift_fst _ _ _`.

Establish `e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left` using `(congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁`. Establish `gG` using `isGrpPullback_pullback t.G (spMap φ)`. Establish `hk₁ : x₁ ^ k = 1` using `ConstGrp.push_injective gG _ (by`. Set `ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N` to `Over.homMk ξ hh`. Establish `e : pushHom gG _ x₁ = ρ ≫ x₀` using `Over.OverMorphism.ext e₁`.

Rewrite using `[map_pow, map_one, e, ← MonObj.comp_pow, hN.g_tors, MonObj.comp_one])`. Establish `hp` using `isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hN.formal)`. Take `⟨g', hg'⟩` from `FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp`. Set `y : TFK (R` to `R) F ⟶ (Over.pullback (jK R)).obj t.G := Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F) (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)`. Establish `hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = ((jFK (R` using `R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by`.

Rewrite using `[← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Conclude with `pullback.lift_fst _ _ _`. Use `⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁ (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩` and prove the remaining obligations. Set `xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G))` to `Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)) (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))`. Establish `hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`.

Establish `c` using `hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)`. Conclude with `⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩`. Rewrite using `[hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]`. Conclude with `Category.assoc _ _ _`.
-/
theorem main : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk N g₀ x₀ hN F _ _ _ x hx q hq hg
  have hL := firstFiveLaws
  have := hN.finite
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, hN.g_tors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hN.formal)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.FinitePartGeneric
