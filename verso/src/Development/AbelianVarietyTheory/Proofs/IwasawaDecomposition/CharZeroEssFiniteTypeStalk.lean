import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.ThetaDedekind
open GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.ThetaNormal
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Use `haveI : IsProper Z.s := ProperFamily.isProper_of_isProjOver Z.proj`. Use `haveI : Flat Z.s := Z.flat`. Set `y : PrimeSpectrum O` to `Z.s z`. Use `letI : Algebra O ((Sp O).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : IsLocalization.AtPrime ((Sp O).presheaf.stalk (Z.s z)) y.asIdeal := StructureSheaf.IsLocalization.to_stalk _ y`.

Set `φ` to `algebraMap O ((Sp O).presheaf.stalk (Z.s z))`. Establish `h₁ : (Z.s.stalkMap z).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap Z.s z`. Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Establish `hφ : Function.Injective φ` using `IsLocalization.injective ((Sp O).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `: IsLocalHom (Z.s.stalkMap z).hom` using `Z.s.toLRSHom.prop z`.

Establish `hσ : Function.Injective (Z.s.stalkMap z).hom` using `LocM.Bdy.injective_of_flat_local _ (Flat.stalkMap Z.s z)`. Use `⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩` and prove the remaining obligations. Establish `hO : Algebra.EssFiniteType ℤ O` using `inferInstance`. Use `RingHom.essFiniteType_algebraMap.1 ?_` and prove the remaining obligations. Use `(RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1` and compare the differences between its conclusion and the goal.

Conclude with `Subsingleton.elim _ _`.
-/
theorem charZero_essFiniteType_stalk [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] (Z : Model Xo c β) (z : Z.X) :
    CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  haveI : IsProper Z.s := ProperFamily.isProper_of_isProjOver Z.proj
  haveI : Flat Z.s := Z.flat
  let y : PrimeSpectrum O := Z.s z
  letI : Algebra O ((Sp O).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp O).presheaf.stalk (Z.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap O ((Sp O).presheaf.stalk (Z.s z))
  have h₁ : (Z.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap Z.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp O).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsLocalHom (Z.s.stalkMap z).hom := Z.s.toLRSHom.prop z
  have hσ : Function.Injective (Z.s.stalkMap z).hom := LocM.Bdy.injective_of_flat_local _ (Flat.stalkMap Z.s z)
  refine ⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ O := inferInstance
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

/- English proof (translation)
Take `⟨⟨_, _⟩, _, hfr⟩` from `hβ`. Use `letI : Algebra O c.F := β.toAlgebra`. Take `⟨_, _, -, -, hfl, hdom, -⟩` from `GlobalTheory.genericPart_dense_proOpen O c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense`. Use `haveI : IsNoetherian Z.X := {}`. Use `haveI : GlobalTheory.IsNormalScheme Z.X := GlobalTheory.IsNormalScheme.of_pred Z.normal`.

Use `haveI : Flat Z.j := hfl`. Use `haveI : IsDominant Z.j := hdom`. Establish `hC` using `irreducibleComponent_mem_irreducibleComponents P`. Establish `hCo : IsOpen (irreducibleComponent P)` using `GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hC`. Establish `hg` using `hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)`.

Establish `hgP : hC.1.genericPoint = P` using `hP _ (hg.specializes mem_irreducibleComponent)`. Take `⟨w, hwC, ⟨v, rfl⟩⟩` from `(Scheme.Hom.denseRange Z.j).inter_open_nonempty _ hCo ⟨P, mem_irreducibleComponent⟩`. Establish `hPw : P ⤳ Z.j v` using `hgP ▸ hg.specializes hwC`. Take `⟨w', -, h₂⟩` from `Flat.generalizingMap Z.j hPw`. Conclude with `⟨w', h₂⟩`.
-/
theorem mem_range_j_of_maximal (hβ : IsDedFrac β) (Z : Model Xo c β) (P : Z.X) (hP : ∀ q : Z.X, q ⤳ P → q = P) :
    P ∈ Set.range Z.j := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨_, _, -, -, hfl, hdom, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense
  haveI : IsNoetherian Z.X := {}
  haveI : GlobalTheory.IsNormalScheme Z.X := GlobalTheory.IsNormalScheme.of_pred Z.normal
  haveI : Flat Z.j := hfl
  haveI : IsDominant Z.j := hdom
  have hC := irreducibleComponent_mem_irreducibleComponents P
  have hCo : IsOpen (irreducibleComponent P) := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hgP : hC.1.genericPoint = P := hP _ (hg.specializes mem_irreducibleComponent)
  obtain ⟨w, hwC, ⟨v, rfl⟩⟩ := (Scheme.Hom.denseRange Z.j).inter_open_nonempty _ hCo ⟨P, mem_irreducibleComponent⟩
  have hPw : P ⤳ Z.j v := hgP ▸ hg.specializes hwC
  obtain ⟨w', -, h₂⟩ := Flat.generalizingMap Z.j hPw
  exact ⟨w', h₂⟩

/- English proof (translation)
Take `⟨⟨_, _⟩, _, hfr⟩` from `id hβ`. Use `letI : Algebra O c.F := β.toAlgebra`. Take `⟨_, _, -, hpre, hfl, -, -⟩` from `GlobalTheory.genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense`. Use `haveI : Flat Y.j := hfl`. Use `haveI : IsPreimmersion Y.j := hpre`.

Take `⟨_, _⟩` from `charZero_essFiniteType_stalk Y x`. Take `⟨_, _⟩` from `Y.normal x`. Take `⟨hdC, hnC⟩` from `AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (Y.X.presheaf.stalk x)`. Establish `hN : IsNoetherianRing (LocM.Bdy.Cpl Y.X x)`. Use `AdicNoeth.isNoetherianRing_of_isAdicComplete _ (maximalIdeal _) ?_ inferInstance (inferInstanceAs (IsNoetherianRing (ResidueField _)))` and prove the remaining obligations.

Rewrite using `[AdicCompletion.maximalIdeal_eq_map]`. Conclude with `(maximalIdeal _).fg_of_isNoetherianRing.map _`. Take `⟨k, _, _, hk, S', hS'⟩` from `CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x`. Use `haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance`. Take `⟨R, _, _, _, _, j, _, _, hj⟩` from `LocM.Bdy.exists_etale_local (LocM.Bdy.Cpl Y.X x) (Y.X.residueField x) k (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x)))`.

Establish `: IsLocalization.AtPrime R (maximalIdeal R)` using `IsLocalization.self fun a ha => by_contra fun h => ha h`. Take `⟨hd, hn⟩` from `isDomain_and_isIntegrallyClosed_atPrime_of_etale (LocM.Bdy.Cpl Y.X x) (maximalIdeal R) R`. Establish `hNR : IsNoetherianRing R` using `IsNoetherianRing.of_finite (LocM.Bdy.Cpl Y.X x) R`. Establish `hc` using `CompleteFiniteExtension.isAdicComplete_of_finite_local (LocM.Bdy.Cpl Y.X x) R`. Establish `f₁` using `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x) (B := LocM.Bdy.Cpl Y.X x)`.

Establish `f₂` using `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := LocM.Bdy.Cpl Y.X x) (B := R)`. Set `ψ : Y.X.presheaf.stalk x →+* R` to `(algebraMap (LocM.Bdy.Cpl Y.X x) R).comp (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x))`. Establish `hinj : Function.Injective ψ` using `(FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)`. Use `haveI : CharZero R := charZero_of_injective_ringHom hinj`. Establish `hadm` using `isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc`.

Establish `hψf : ψ.Flat` using `RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) (RingHom.flat_algebraMap_iff.2 inferInstance)`. Use `haveI : IsLocalHom ψ := inferInstance`. Take `⟨t, ⟨m⟩⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t`. Establish `hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j`. Introduce and unpack `_ ⟨q, rfl⟩`.

Rewrite using `[Scheme.Hom.comp_apply]`. Establish `h0 : (jK R q).asIdeal = ⊥`. Establish `h0 : q.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime`. Express the relevant statement in the definitionally equal form `Ideal.comap _ q.asIdeal = ⊥`. Rewrite using `[h0, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]`.

Conclude with `mem_range_j_of_maximal hβ Y _ fun y hy => LocM.Bdy.generic_image x ψ hinj _ h0 y hy`. Take `⟨y, hy⟩` from `HomExt.exists_lift_of_range_subset Y.j _ hr`. Establish `hpol : LN.PolAt t (jK R)` using `GoodTrait.polAt_of_point Y m (jK R) y hy`. Establish `h₁` using `LocM.Bdy.residue_comp (R := R) x`. Establish `e : spMap (algebraMap (LocM.Bdy.Cpl Y.X x) R) ≫ fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x`.

Rewrite using `[spMap_comp, Category.assoc]`. Both sides reduce to the same expression. Establish `h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) = spMap ((ResidueField.map (algebraMap (LocM.Bdy.Cpl Y.X x) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x))))` using `(spMap_comp _ _).symm.trans (congrArg spMap hj)`. Take `⟨S₁, hS₁⟩` from `LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by`. Rewrite using `[← Category.assoc]`.

Use `(congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_` and prove the remaining obligations. Conclude with `h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m`. Establish `hsplit : LN.SplitOver t.G (maximalIdeal R)` using `⟨S₁, hS₁⟩`. Establish `hθ` using `thetaNZ_of_polAt E H R hadm t hpol hsplit`. Conclude with `exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ`.
-/
theorem exists_theta (hβ : IsDedFrac β) [Algebra.FiniteType ℤ O] (Y : Model Xo c β) (x : Y.X)
    [PerfectField (Y.X.residueField x)] :
    ∃ V : Y.X.Opens, x ∈ V ∧ ∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i) := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := id hβ
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨_, _, -, hpre, hfl, -, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  haveI : Flat Y.j := hfl
  haveI : IsPreimmersion Y.j := hpre
  obtain ⟨_, _⟩ := charZero_essFiniteType_stalk Y x
  obtain ⟨_, _⟩ := Y.normal x
  obtain ⟨hdC, hnC⟩ := AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (Y.X.presheaf.stalk x)
  have hN : IsNoetherianRing (LocM.Bdy.Cpl Y.X x) := by
    refine AdicNoeth.isNoetherianRing_of_isAdicComplete _ (maximalIdeal _) ?_ inferInstance
      (inferInstanceAs (IsNoetherianRing (ResidueField _)))
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (maximalIdeal _).fg_of_isNoetherianRing.map _
  obtain ⟨k, _, _, hk, S', hS'⟩ := CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x
  haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := LocM.Bdy.exists_etale_local (LocM.Bdy.Cpl Y.X x) (Y.X.residueField x) k
    (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x)))
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale (LocM.Bdy.Cpl Y.X x) (maximalIdeal R) R
  have hNR : IsNoetherianRing R := IsNoetherianRing.of_finite (LocM.Bdy.Cpl Y.X x) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local (LocM.Bdy.Cpl Y.X x) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x) (B := LocM.Bdy.Cpl Y.X x)
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := LocM.Bdy.Cpl Y.X x) (B := R)
  let ψ : Y.X.presheaf.stalk x →+* R :=
    (algebraMap (LocM.Bdy.Cpl Y.X x) R).comp (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x))
  have hinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hadm := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc
  have hψf : ψ.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : IsLocalHom ψ := inferInstance
  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t
  have hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have h0 : (jK R q).asIdeal = ⊥ := by
      have h0 : q.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime
      change Ideal.comap _ q.asIdeal = ⊥
      rw [h0, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]
    exact mem_range_j_of_maximal hβ Y _ fun y hy => LocM.Bdy.generic_image x ψ hinj _ h0 y hy
  obtain ⟨y, hy⟩ := HomExt.exists_lift_of_range_subset Y.j _ hr
  have hpol : LN.PolAt t (jK R) := GoodTrait.polAt_of_point Y m (jK R) y hy
  have h₁ := LocM.Bdy.residue_comp (R := R) x
  have e : spMap (algebraMap (LocM.Bdy.Cpl Y.X x) R) ≫ fromSpecCompletedStalk Y.X x =
      spMap ψ ≫ Y.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  have h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) =
      spMap ((ResidueField.map (algebraMap (LocM.Bdy.Cpl Y.X x) R)).comp
        (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (LocM.Bdy.Cpl Y.X x)))) :=
    (spMap_comp _ _).symm.trans (congrArg spMap hj)
  obtain ⟨S₁, hS₁⟩ := LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by
    rw [← Category.assoc]
    refine (congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_
    exact h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m
  have hsplit : LN.SplitOver t.G (maximalIdeal R) := ⟨S₁, hS₁⟩
  have hθ := thetaNZ_of_polAt E H R hadm t hpol hsplit
  exact exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ

/- English proof (translation)
Introduce `x`. Use `haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj`. Use `haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s`. Take `⟨x₀, hx₀, hcl⟩` from `(isClosed_closure (s := {x})).exists_closed_singleton ⟨x, subset_closure rfl⟩`. Use `haveI : LocallyOfFiniteType (spMap (algebraMap ℤ O)) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)`.

Use `haveI := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (Y.s ≫ spMap (algebraMap ℤ O)) x₀ hcl`. Take `⟨V, hV, h⟩` from `exists_theta hβ Y x₀`. Conclude with `⟨V, (specializes_iff_mem_closure.2 hx₀).mem_open V.isOpen hV, h⟩`.
-/
theorem hasTheta (hβ : IsDedFrac β) [Algebra.FiniteType ℤ O] (Y : Model Xo c β) : HasTheta Y.t.G Y.t.PP.L := by
  intro x
  haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj
  haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  obtain ⟨x₀, hx₀, hcl⟩ := (isClosed_closure (s := {x})).exists_closed_singleton ⟨x, subset_closure rfl⟩
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ O)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (Y.s ≫ spMap (algebraMap ℤ O)) x₀ hcl
  obtain ⟨V, hV, h⟩ := exists_theta hβ Y x₀
  exact ⟨V, (specializes_iff_mem_closure.2 hx₀).mem_open V.isOpen hV, h⟩

/- English proof (translation)
The claim follows from `GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H D l _ _ _ _ _ _ Y.oF _ β (ofModel Y) hβ (hasTheta hβ Y)`.
-/
theorem pushInvertible (hβ : IsDedFrac β) [Algebra.FiniteType ℤ O] (Y : Model Xo c β) :
    PushInvertible Y.t.G Y.t.PP.L :=
  GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H D l _ _ _ _ _ _ Y.oF _
    β (ofModel Y) hβ (hasTheta hβ Y)

/- English proof (translation)
Take `⟨⟨_, _⟩, -, -⟩` from `id hβ`. Conclude with `GlobalTheory.FlagMod.isLB_detOm (pushInvertible hβ Y)`.
-/
theorem isLB_detOm (hβ : IsDedFrac β) [Algebra.FiniteType ℤ O] (Y : Model Xo c β) : (GlobalTheory.FlagMod.detOm Y).IsLB := by
  obtain ⟨⟨_, _⟩, -, -⟩ := id hβ
  exact GlobalTheory.FlagMod.isLB_detOm (pushInvertible hβ Y)

end GlobalTheory.ThetaDedekind
