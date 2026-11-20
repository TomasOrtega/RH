import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigCube

/- English proof (translation)
Establish `: IsProper ((Over.pullback (jK R)).obj G).hom` using `hp`. Use `Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG (IsPullback.of_hasPullback G.hom (jK R)))` and prove the remaining obligations. Rewrite using `[genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]`. Introduce and unpack `_ rfl`. Use `⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations.

Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))`.
-/
theorem genericPoints_subset_abLocus {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) : genericPoints (Sp R) ⊆ abLocus G := by
  have : IsProper ((Over.pullback (jK R)).obj G).hom := hp
  refine Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG
    (IsPullback.of_hasPullback G.hom (jK R)))
  rw [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]
  rintro _ rfl
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

/- English proof (translation)
Set `j` to `jK R`. Set `A : Over (Spec (CommRingCat.of (FractionRing R)))` to `(Over.pullback j).obj G`. Establish `gp : IsGrpPullback A G j (pullback.fst G.hom j)` using `isGrpPullback_pullback G j`. Establish `hA : IsSemiAbelian A` using `IsSemiAbelian.pullback j G hG`. Establish `: IsProper A.hom` using `hp`.

Establish `hAb : IsAbelianScheme A` using `AbelianSchemeGerms.isAbelianScheme_of_proper A hA`. Use `hA.comm` as an intermediate fact. Set `P : Over (Spec (CommRingCat.of (FractionRing R)))` to `Over.mk (pullback.snd (G3 G).hom j)`. Set `x : Fin 3 → (P ⟶ A)` to `fun i => Over.homMk (gp.1.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by`. Rewrite using `[Category.assoc, Over.w]`.

Conclude with `pullback.condition)) (gp.1.lift_snd _ _ _)`. Set `U : Over.mk (P.hom ≫ j) ⟶ G3 G` to `Over.homMk (pullback.fst (G3 G).hom j) pullback.condition`. Establish `hx : ∀ i, pushPt gp.1.w (x i) = U ≫ x3 G i` using `fun i => Over.OverMorphism.ext (gp.1.lift_fst _ _ _)`. Set `πA` to `pullback.fst G.hom j`. Set `pf` to `pullback.fst (G3 G).hom j`.

Take `⟨t₀, ht₀⟩` from `GlobalTheory.CubeTop.cubeTheorem _ A hAb (M.pull πA) (pull_isLB hM _) P (x 0) (x 1) (x 2)`. Take `⟨t₁, ht₁⟩` from `CubeDescent.exists_gen_comp M πA _ _ t₀ ht₀`. Set `y : Fin 3 → (Over.mk (P.hom ≫ j) ⟶ G)` to `fun i => U ≫ x3 G i`. Establish `key : ∀ z : P ⟶ A, z.left ≫ πA = (pushHom gp P z).left` using `fun z => rfl`. Establish `hxp : ∀ i, pushHom gp P (x i) = y i` using `hx`.

Apply the tactic sequence `have e : lift (y 0) (lift (y 1) (y 2)) = U := by ext <;> simp [y, x3]`. Take `⟨t₂, ht₂, -⟩` from `exists_gen hM (φ' := fun I => pf ≫ thφ G (x3 G) I) (ε' := thε) (fun V _ h => by`. Establish `hθ` using `prod_cub (y 0) (y 1) (y 2) h`. Rewrite `hθ` using `[e]`. Use `Eq.trans ?_ hθ.symm` and prove the remaining obligations.

Simplify using `only [Fin.prod_univ_eight, key, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_mul, map_one, hxp, zpow_one, zpow_neg_one]`. Simplify using `only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, key, map_mul, map_one, hxp, zpow_one, zpow_neg_one]) t₁ ht₁`. Set `c` to `CechPic.cls M hM`. Use `(CechPic.cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hM _ _) pf)).1 ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull (LB.isLB_linComb hM _ _), CechPic.cls_linComb hM, map_sum]`.

Simplify using `only [map_zsmul, ← CechPic.pull_comp]`. Establish `h2` using `(CechPic.cls_eq_zero_iff (LB.isLB_linComb hM (fun I => pf ≫ thφ G (x3 G) I) thε)).2 ⟨t₂, ht₂⟩`. Rewrite `h2` using `[CechPic.cls_linComb hM]`. Conclude with `h2`.
-/
theorem exists_gen_theta_generic {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) {M : LB G.left} (hM : M.IsLB) :
    ∃ t : ((Theta G M).pull (pullback.fst (G3 G).hom (jK R))).Gen, t.IsGen := by
  let j := jK R
  let A : Over (Spec (CommRingCat.of (FractionRing R))) := (Over.pullback j).obj G
  have gp : IsGrpPullback A G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  have hA : IsSemiAbelian A := IsSemiAbelian.pullback j G hG
  have : IsProper A.hom := hp
  have hAb : IsAbelianScheme A := AbelianSchemeGerms.isAbelianScheme_of_proper A hA
  have := hA.comm
  let P : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk (pullback.snd (G3 G).hom j)
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (gp.1.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (gp.1.lift_snd _ _ _)
  let U : Over.mk (P.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
  have hx : ∀ i, pushPt gp.1.w (x i) = U ≫ x3 G i := fun i => Over.OverMorphism.ext (gp.1.lift_fst _ _ _)
  let πA := pullback.fst G.hom j
  let pf := pullback.fst (G3 G).hom j
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.CubeTop.cubeTheorem _ A hAb (M.pull πA) (pull_isLB hM _) P (x 0) (x 1) (x 2)
  obtain ⟨t₁, ht₁⟩ := CubeDescent.exists_gen_comp M πA _ _ t₀ ht₀
  let y : Fin 3 → (Over.mk (P.hom ≫ j) ⟶ G) := fun i => U ≫ x3 G i
  have key : ∀ z : P ⟶ A, z.left ≫ πA = (pushHom gp P z).left := fun z => rfl
  have hxp : ∀ i, pushHom gp P (x i) = y i := hx
  have e : lift (y 0) (lift (y 1) (y 2)) = U := by ext <;> simp [y, x3]
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hM (φ' := fun I => pf ≫ thφ G (x3 G) I) (ε' := thε) (fun V _ h => by
    have hθ := prod_cub (y 0) (y 1) (y 2) h
    rw [e] at hθ
    refine Eq.trans ?_ hθ.symm
    simp only [Fin.prod_univ_eight, key, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_mul, map_one, hxp, zpow_one, zpow_neg_one]
    simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, key, map_mul, map_one, hxp,
      zpow_one, zpow_neg_one]) t₁ ht₁
  let c := CechPic.cls M hM
  refine (CechPic.cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hM _ _) pf)).1 ?_
  rw [CechPic.cls_pull (LB.isLB_linComb hM _ _), CechPic.cls_linComb hM, map_sum]
  simp only [map_zsmul, ← CechPic.pull_comp]
  have h2 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM (fun I => pf ≫ thφ G (x3 G) I) thε)).2 ⟨t₂, ht₂⟩
  rw [CechPic.cls_linComb hM] at h2
  exact h2

/- English proof (translation)
Introduce `R _ _ _ _ _ G _ _ hG hp M hM`. Establish `hab` using `genericPoints_subset_abLocus G hG hp`. Establish `a₁` using `hG.smooth`. Use `hG.geomConnected` as an intermediate fact. Establish `b₁` using `GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G`.

Take `⟨a₂, b₂, -⟩` from `GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁`. Take `⟨a₃, b₃, -⟩` from `GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂`. Take `⟨r, hr⟩` from `DVR.exists_gen_of_isLB_local (V := R) (M.pull (eSec G)) (pull_isLB hM _)`. Set `L : RigLB G` to `⟨M, r, hM, hr⟩`. Establish `hΘ : (Theta G M).IsLB` using `LB.isLB_linComb hM _ _`.

Establish `h₁ : IsPreimmersion (jK R)` using `IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `h₂ : Flat (jK R)`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))`. Set `e : 𝟙_ (Over (Sp R)) ⟶ G3 G` to `lift 1 (lift 1 1)`.

Take `⟨t, ht⟩` from `GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂ DVR.isDominant_jK inferInstance (G3 G) e.left (Theta G M) (Over.w e) a₃ b₃ hΘ (DVR.exists_gen_of_isLB_local _ (pull_isLB hΘ _)) (exists_gen_theta_generic G hG hp hM)`. Take `⟨c⟩` from `(CubeGen.cubical_and_symmetric (Sp R) G L hG ⟨inferInstance, hab⟩).1 ⟨t, ht⟩`. Conclude with `⟨L, c, rfl⟩`.
-/
theorem exists_rigLB_cubicalStr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ M : LB G.left, M.IsLB → ∃ (L : RigLB G) (_ : CubicalStr G L), L.L = M := by
  intro R _ _ _ _ _ G _ _ hG hp M hM
  have hab := genericPoints_subset_abLocus G hG hp
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨a₂, b₂, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁
  obtain ⟨a₃, b₃, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := R) (M.pull (eSec G)) (pull_isLB hM _)
  let L : RigLB G := ⟨M, r, hM, hr⟩
  have hΘ : (Theta G M).IsLB := LB.isLB_linComb hM _ _
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift 1 (lift 1 1)
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (G3 G) e.left (Theta G M) (Over.w e) a₃ b₃ hΘ
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hΘ _)) (exists_gen_theta_generic G hG hp hM)
  obtain ⟨c⟩ := (CubeGen.cubical_and_symmetric (Sp R) G L hG ⟨inferInstance, hab⟩).1 ⟨t, ht⟩
  exact ⟨L, c, rfl⟩

end GlobalTheory.RigCube
