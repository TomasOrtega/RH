import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLift

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.PolBundleLocEt

open GlobalTheory.PolRoot GlobalTheory.PolBundleLoc

/- English proof (translation)
Introduce `o _ ζ g n F R _ _ _ hR y`. Use `haveI : IsAdicComplete (maximalIdeal R) R := hR`. Use `haveI : HenselianLocalRing R := { is_henselian := fun f hf a₀ h₁ h₂ => HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }`. Establish `hAb` using `F.univ.ab`. Establish `hP` using `F.univ.isLB`.

Set `k` to `ResidueField R`. Set `t₀ : Sp k ⟶ F.X` to `spMap (residue R) ≫ y`. Establish `h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀)` using `root_geom F (AlgebraicClosure k) _`. Take `⟨B, hB, h₂⟩` from `GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁`. Use `haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB`.

Use `haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩`. Use `haveI : Module.Finite k B := Algebra.IsIntegral.finite`. Take `⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩` from `GlobalTheory.T.exists_complete_local_geomDomain' k B inferInstance`. Set `tC : Sp C ⟶ F.X` to `spMap (algebraMap k C) ≫ t₀`. Establish `h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC)`.

Use `root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))` and prove the remaining obligations. Simplify using `only [tC, ← Category.assoc, spMap_comp']`. Use `congr 2`. Conclude with `ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))`. Establish `h₄ : Root F.univ.A F.univ.P tC` using `GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃`.

Take `⟨B', hB', h₅⟩` from `GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ C h₄`. Establish `hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B')`. Introduce `K _ _ h1 h2`. Use `haveI := hdom K h1 h2`. Set `m : K ⊗[k] B' →ₐ[K] K ⊗[k] C` to `Algebra.TensorProduct.map (AlgHom.id K K) B'.val`.

Establish `hm : Function.Injective m`. Use `Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap) Subtype.val_injective` as an intermediate fact. Conclude with `this`. Conclude with `hm.isDomain m`. Take `⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩` from `GlobalTheory.T.exists_separable_point_of_geometrically_domain k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'`.

Establish `h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀)`. Use `root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_comp']`. Use `congr 2`. Conclude with `ψ.comp_algebraMap`.

Use `haveI : Module.Finite (ResidueField R) k'' := hfin`. Use `haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep`. Take `⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩` from `exists_etale_lift_of_isSeparable R k''`. Use `haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'`. Use `haveI : IsLocalHom (algebraMap R R') := ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)`.

Establish `hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R'` using `Algebra.FormallyUnramified.map_maximalIdeal`. Establish `hcR' : IsAdicComplete (maximalIdeal R') R'`. Use `isAdicComplete_map_of_finite (maximalIdeal R) R'` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis. Use `haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance`.

Set `ρ : R →+* R'` to `algebraMap R R'`. Take `⟨φ, hφ⟩` from `residue_lift R R' k'' ε`. Set `T : Sp R' ⟶ F.X` to `spMap ρ ≫ y`. Establish `h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T)`. Use `root_congr ?_ (h₆.comp hAb (spMap φ))` and prove the remaining obligations.

Simplify using `only [T, t₀, ← Category.assoc, spMap_comp']`. Use `congr 2`. Rewrite using `[← RingHom.comp_assoc, hφ]`. Conclude with `(ResidueField.map_comp_residue ρ).symm`. Take `⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩` from `GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇`.

Establish `hB₁ : IsAbelianScheme B₁` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ`. Establish `hP' : (F.univ.P.pull β₂).IsLB` using `ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _`. Establish `hker` using `GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2`. Take `⟨M, hM, ⟨hcub⟩⟩` from `exists_rigLB_cubical R' B₁ hB₁ L hL`. Establish `hK` using `GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ`.

Establish `hA` using `GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal F R' T B₁ β β₂ hβ hsq L hL hΛ`. Substitute `hM` using the available equality. Establish `hinj : Function.Injective ρ`. Use `letI : Algebra.Etale R R' := het`. Use `haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Conclude with `FaithfulSMul.algebraMap_injective R R'`. Conclude with `⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR, RingHom.etale_algebraMap.mpr het, B₁, inferInstance, inferInstance, β, β₂, M, hcub, hβ, hsq, hA, hK, hΛ⟩`.
-/
theorem exists_rigLB_sFam_etale :
    ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.Etale ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro o _ ζ g n F R _ _ _ hR y
  haveI : IsAdicComplete (maximalIdeal R) R := hR
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have hAb := F.univ.ab
  have hP := F.univ.isLB
  let k := ResidueField R
  let t₀ : Sp k ⟶ F.X := spMap (residue R) ≫ y

  have h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀) :=
    root_geom F (AlgebraicClosure k) _

  obtain ⟨B, hB, h₂⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁
  haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩
  haveI : Module.Finite k B := Algebra.IsIntegral.finite

  obtain ⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩ := GlobalTheory.T.exists_complete_local_geomDomain' k B inferInstance
  let tC : Sp C ⟶ F.X := spMap (algebraMap k C) ≫ t₀
  have h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC) := by
    refine root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))
    simp only [tC, ← Category.assoc, spMap_comp']
    congr 2
    exact ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))
  have h₄ : Root F.univ.A F.univ.P tC :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃

  obtain ⟨B', hB', h₅⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ C h₄
  have hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B') := by
    intro K _ _ h1 h2
    haveI := hdom K h1 h2
    let m : K ⊗[k] B' →ₐ[K] K ⊗[k] C := Algebra.TensorProduct.map (AlgHom.id K K) B'.val
    have hm : Function.Injective m := by
      have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap)
        Subtype.val_injective
      exact this
    exact hm.isDomain m
  obtain ⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩ := GlobalTheory.T.exists_separable_point_of_geometrically_domain k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'
  have h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀) := by
    refine root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact ψ.comp_algebraMap

  haveI : Module.Finite (ResidueField R) k'' := hfin
  haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep
  obtain ⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R k''
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := Algebra.FormallyUnramified.map_maximalIdeal
  have hcR' : IsAdicComplete (maximalIdeal R') R' := by
    have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this
  haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance
  let ρ : R →+* R' := algebraMap R R'
  obtain ⟨φ, hφ⟩ := residue_lift R R' k'' ε
  let T : Sp R' ⟶ F.X := spMap ρ ≫ y
  have h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T) := by
    refine root_congr ?_ (h₆.comp hAb (spMap φ))
    simp only [T, t₀, ← Category.assoc, spMap_comp']
    congr 2
    rw [← RingHom.comp_assoc, hφ]
    exact (ResidueField.map_comp_residue ρ).symm
  obtain ⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩ :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ
  have hP' : (F.univ.P.pull β₂).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _
  have hker := GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2
  obtain ⟨M, hM, ⟨hcub⟩⟩ := exists_rigLB_cubical R' B₁ hB₁ L hL
  have hK := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ
  have hA := GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal F R' T B₁ β β₂ hβ hsq L hL hΛ
  subst hM
  have hinj : Function.Injective ρ := by
    letI : Algebra.Etale R R' := het
    haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective R R'
  exact ⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR,
    RingHom.etale_algebraMap.mpr het, B₁, inferInstance, inferInstance, β, β₂, M, hcub,
    hβ, hsq, hA, hK, hΛ⟩

end GlobalTheory.PolBundleLocEt
