import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimcpl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomainStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautEtaleB

/- English proof (translation)
Set `B` to `AdicCompletion (maximalIdeal A) A`. Use `haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _`. Take `⟨ψ, hψl, hψ⟩` from `GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp A R hR φ hφ`. Establish `hmap : (maximalIdeal B).map ψ = (maximalIdeal A).map φ`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]`.

Establish `hresψ : ((residue R).comp ψ).Finite`. Establish `e : ((residue R).comp ψ).comp (algebraMap A B) = (residue R).comp φ`. Rewrite using `[RingHom.comp_assoc, hψ]`. Conclude with `RingHom.Finite.of_comp_finite (e ▸ hres)`. Establish `hfin : ψ.Finite` using `GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama B R ψ inferInstance hψl (hmap ▸ hprim) hresψ`.

Establish `hdB : ringKrullDim R = ringKrullDim B` using `by rw [hdim, UpperTheory.V.CA.g_dimcpl]`. Establish `hi : Function.Injective ψ` using `GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain B R ψ hfin hdB`. Establish `hs : Function.Surjective ψ` using `GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal B R ψ inferInstance hi hfin (fun R' _ _ _ _ _ _ hR' f g hf' hg' hf hg h => hinj R' hR' f g hf' hg' hf hg (by`. Rewrite using `[← hψ, ← RingHom.comp_assoc, h, RingHom.comp_assoc]))`. Use `⟨?_, ?_, hres⟩` and prove the remaining obligations.

Rewrite using `[← hψ]`. Use `RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) ?_` and prove the remaining obligations. Conclude with `RingHom.Flat.of_bijective ⟨hi, hs⟩`. Rewrite using `[← hmap]`. Conclude with `map_maximalIdeal_of_surjective ψ hs`.
-/
theorem isEtaleCompletion_of_forall_eq_inj (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    (hAd : IsDomain (AdicCompletion (maximalIdeal A) A))
    (hAn : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A))
    (hR : IsAdicComplete (maximalIdeal R) R) (φ : A →+* R) (hφ : IsLocalHom φ)
    (hprim : maximalIdeal R ≤ ((maximalIdeal A).map φ).radical)
    (hres : ((residue R).comp φ).Finite) (hdim : ringKrullDim R = ringKrullDim A)
    (hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp φ = g.comp φ → f = g) :
    GlobalTheory.Toroidal.IsEtaleCompletion φ := by
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp A R hR φ hφ
  have hmap : (maximalIdeal B).map ψ = (maximalIdeal A).map φ := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  have hresψ : ((residue R).comp ψ).Finite := by
    have e : ((residue R).comp ψ).comp (algebraMap A B) = (residue R).comp φ := by
      rw [RingHom.comp_assoc, hψ]
    exact RingHom.Finite.of_comp_finite (e ▸ hres)
  have hfin : ψ.Finite := GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama B R ψ inferInstance hψl (hmap ▸ hprim) hresψ
  have hdB : ringKrullDim R = ringKrullDim B := by rw [hdim, UpperTheory.V.CA.g_dimcpl]
  have hi : Function.Injective ψ := GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain B R ψ hfin hdB
  have hs : Function.Surjective ψ := GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal B R ψ inferInstance hi hfin
    (fun R' _ _ _ _ _ _ hR' f g hf' hg' hf hg h => hinj R' hR' f g hf' hg' hf hg (by
      rw [← hψ, ← RingHom.comp_assoc, h, RingHom.comp_assoc]))
  refine ⟨?_, ?_, hres⟩
  · rw [← hψ]
    refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) ?_
    exact RingHom.Flat.of_bijective ⟨hi, hs⟩
  · rw [← hmap]
    exact map_maximalIdeal_of_surjective ψ hs

/- English proof (translation)
Set `y : PrimeSpectrum K` to `f x`. Use `letI : Algebra K ((Sp K).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : IsLocalization.AtPrime ((Sp K).presheaf.stalk (f x)) y.asIdeal := StructureSheaf.IsLocalization.to_stalk _ y`. Set `φ` to `algebraMap K ((Sp K).presheaf.stalk (f x))`. Establish `h₁ : (f.stalkMap x).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap f x`.

Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Establish `hσ : Function.Injective ((f.stalkMap x).hom.comp φ)` using `RingHom.injective _`. Use `⟨charZero_of_injective_ringHom hσ, ?_⟩` and prove the remaining obligations. Establish `hQ : Algebra.EssFiniteType ℤ ℚ` using `Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)`. Establish `hK : Algebra.EssFiniteType ℤ K` using `Algebra.EssFiniteType.comp ℤ ℚ K`.

Use `RingHom.essFiniteType_algebraMap.1 ?_` and prove the remaining obligations. Use `(RingHom.essFiniteType_algebraMap.2 hK).comp (h₂.comp h₁) using 1` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.
-/
theorem charZero_essFiniteType_stalk (K : Type) [Field K] [CharZero K] [FiniteDimensional ℚ K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] (x : X) :
    CharZero (X.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  let y : PrimeSpectrum K := f x
  letI : Algebra K ((Sp K).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp K).presheaf.stalk (f x)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap K ((Sp K).presheaf.stalk (f x))
  have h₁ : (f.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hσ : Function.Injective ((f.stalkMap x).hom.comp φ) := RingHom.injective _
  refine ⟨charZero_of_injective_ringHom hσ, ?_⟩
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hK : Algebra.EssFiniteType ℤ K := Algebra.EssFiniteType.comp ℤ ℚ K
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hK).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

/- English proof (translation)
Establish `hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ)` using `(IsFractionRing.injective B (FractionRing B)).comp hψ`. Set `fK : FractionRing A →+* FractionRing B` to `IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg`. Establish `e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ`. Use extensionality with `x`. Rewrite using `[RingHom.comp_apply]`.

Conclude with `IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x`. Use `⟨fK, ?_⟩` and prove the remaining obligations. Establish `e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK = CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B))`. Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]`. Establish `e2` using `congrArg Spec.map e1`.

Rewrite `e2` using `[Spec.map_comp, Spec.map_comp]`. Conclude with `e2`.
-/
theorem exists_fracMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT ξ hξ`. Take `⟨hqf, hfin⟩` from `GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C hT ξ hξ`. Establish `hdimS` using `ringKrullDim_stalk_eq_of_isTaut hU C hT.1 ξ hξ hfin`. Use `haveI hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance`. Establish `hAdm` using `GlobalTheory.MumfordChart.admissibleBase_chartRing k m e`.

Use `haveI : IsNoetherianRing (ChartRing k m e) := hAdm.1`. Use `haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1`. Establish `hRc : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e)` using `hAdm.2.2.2`. Establish `hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞)`. Rewrite using `[GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]`.

Simplify using `[Nat.card_sum]`. Take `⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, -, hji, -⟩, -⟩` from `hU`. Use `haveI : LocallyOfFiniteType (π ≫ zs) := by`. Take `⟨M, i', hi', hcomp⟩` from `hproj`. Use `haveI := hi'`.

Use `haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M`. Rewrite using `[← hcomp]`. Use `infer_instance`. Use `haveI := c.fin`. Use `set x := ξ (closedPoint (ChartRing k m e)) with hx`.

Use `haveI : IsDomain (S.presheaf.stalk x) := hnorm.isDomain_stalk x`. Use `haveI : IsIntegrallyClosed (S.presheaf.stalk x) := hnorm.isIntegrallyClosed_stalk x`. Take `⟨hc0, hess⟩` from `charZero_essFiniteType_stalk c.F (π ≫ zs) x`. Use `haveI := hc0`. Use `haveI := hess`.

Use `haveI : IsNoetherianRing (S.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _`. Take `⟨hAd, hAn⟩` from `GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed (S.presheaf.stalk x)`. Use `set ψ := (Scheme.stalkClosedPointTo ξ).hom with hψ`. Establish `eξ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `hpt : ∀ p : Sp (ChartRing k m e), ξ p = S.fromSpecStalk x (Spec.map (Scheme.stalkClosedPointTo ξ) p)`.

Introduce `p`. Use `conv_lhs => rw [← eξ]`. Both sides reduce to the same expression. Establish `hprim : maximalIdeal (ChartRing k m e) ≤ ((maximalIdeal (S.presheaf.stalk x)).map ψ).radical`. Introduce `r hr`.

Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hle, hP⟩`. Establish `hc : Ideal.comap ψ P = maximalIdeal (S.presheaf.stalk x)` using `((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hle)).symm`. Establish `hq : (⟨P, hP⟩ : Sp (ChartRing k m e)) = closedPoint (ChartRing k m e)`. Use `hqf _ ((hpt _).trans (Eq.trans ?_ (hpt (closedPoint _)).symm))` and prove the remaining obligations.

Use `congr 1`. Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Use `show Ideal.comap ψ P = Ideal.comap ψ (maximalIdeal (ChartRing k m e))`. Rewrite using `[hc]`. Use `le_antisymm ?_ (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top))` and prove the remaining obligations.

Introduce `a ha`. Conclude with `map_nonunit ψ a ha`. Establish `hP' : P = maximalIdeal (ChartRing k m e)` using `congrArg PrimeSpectrum.asIdeal hq`. Rewrite using `[hP']`. Conclude with `hr`.

Establish `hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : ChartRing k m e →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp …`. Introduce `R' _ _ _ _ _ _ hR' f g hfi hgi hfl hgl hfg`. Establish `hB : GlobalTheory.Mum.Base R'` using `⟨⟨inferInstance, inferInstance, inferInstance, hR'⟩, inferInstance⟩`. Take `⟨fK, hfK⟩` from `exists_fracMap f hfi`. Take `⟨gK, hgK⟩` from `exists_fracMap g hgi`.

Take `⟨-, -, -, hInj, -⟩` from `hT.1`. Use `hInj R' hB f g hfi hgi hfl hgl (spMap fK) (spMap gK) hfK hgK ?_` and prove the remaining obligations. Establish `hsp : spMap f ≫ Spec.map (Scheme.stalkClosedPointTo ξ) = spMap g ≫ Spec.map (Scheme.stalkClosedPointTo ξ)`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `a`. Conclude with `congrArg (fun h : S.presheaf.stalk x →+* R' => h a) hfg`. Establish `hfξ : spMap f ≫ ξ = spMap g ≫ ξ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, hsp, Category.assoc]`.

Use `_ = spMap g ≫ ξ := by rw [eξ]`. Rewrite using `[← cancel_mono j, Category.assoc, Category.assoc, hξ, ← Category.assoc, ← Category.assoc, hfK, hgK, Category.assoc, Category.assoc, hfξ]`. Conclude with `isEtaleCompletion_of_forall_eq_inj (S.presheaf.stalk x) (ChartRing k m e) hAd hAn hRc ψ inferInstance hprim hfin (by rw [hdimR, hdimS]) hinj`.
-/
theorem tautB_isEtaleCompletion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT ξ hξ
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C hT ξ hξ
  have hdimS := ringKrullDim_stalk_eq_of_isTaut hU C hT.1 ξ hξ hfin
  haveI hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsNoetherianRing (ChartRing k m e) := hAdm.1
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  have hRc : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) := hAdm.2.2.2
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, -, hji, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI := c.fin
  set x := ξ (closedPoint (ChartRing k m e)) with hx
  haveI : IsDomain (S.presheaf.stalk x) := hnorm.isDomain_stalk x
  haveI : IsIntegrallyClosed (S.presheaf.stalk x) := hnorm.isIntegrallyClosed_stalk x
  obtain ⟨hc0, hess⟩ := charZero_essFiniteType_stalk c.F (π ≫ zs) x
  haveI := hc0
  haveI := hess
  haveI : IsNoetherianRing (S.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hAd, hAn⟩ := GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed (S.presheaf.stalk x)
  set ψ := (Scheme.stalkClosedPointTo ξ).hom with hψ
  have eξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hpt : ∀ p : Sp (ChartRing k m e), ξ p = S.fromSpecStalk x (Spec.map (Scheme.stalkClosedPointTo ξ) p) := by
    intro p
    conv_lhs => rw [← eξ]
    rfl
  have hprim : maximalIdeal (ChartRing k m e) ≤ ((maximalIdeal (S.presheaf.stalk x)).map ψ).radical := by
    intro r hr
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hle, hP⟩
    have hc : Ideal.comap ψ P = maximalIdeal (S.presheaf.stalk x) :=
      ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hle)).symm
    have hq : (⟨P, hP⟩ : Sp (ChartRing k m e)) = closedPoint (ChartRing k m e) := by
      refine hqf _ ((hpt _).trans (Eq.trans ?_ (hpt (closedPoint _)).symm))
      congr 1
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ψ P = Ideal.comap ψ (maximalIdeal (ChartRing k m e))
      rw [hc]
      refine le_antisymm ?_ (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top))
      intro a ha
      exact map_nonunit ψ a ha
    have hP' : P = maximalIdeal (ChartRing k m e) := congrArg PrimeSpectrum.asIdeal hq
    rw [hP']
    exact hr
  have hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : ChartRing k m e →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp ψ = g.comp ψ → f = g := by
    intro R' _ _ _ _ _ _ hR' f g hfi hgi hfl hgl hfg
    have hB : GlobalTheory.Mum.Base R' := ⟨⟨inferInstance, inferInstance, inferInstance, hR'⟩, inferInstance⟩
    obtain ⟨fK, hfK⟩ := exists_fracMap f hfi
    obtain ⟨gK, hgK⟩ := exists_fracMap g hgi
    obtain ⟨-, -, -, hInj, -⟩ := hT.1
    refine hInj R' hB f g hfi hgi hfl hgl (spMap fK) (spMap gK) hfK hgK ?_
    have hsp : spMap f ≫ Spec.map (Scheme.stalkClosedPointTo ξ) = spMap g ≫ Spec.map (Scheme.stalkClosedPointTo ξ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact congrArg (fun h : S.presheaf.stalk x →+* R' => h a) hfg
    have hfξ : spMap f ≫ ξ = spMap g ≫ ξ := by
      calc spMap f ≫ ξ = spMap f ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by rw [eξ]
        _ = spMap g ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by
          rw [← Category.assoc, hsp, Category.assoc]
        _ = spMap g ≫ ξ := by rw [eξ]
    rw [← cancel_mono j, Category.assoc, Category.assoc, hξ, ← Category.assoc, ← Category.assoc, hfK, hgK,
      Category.assoc, Category.assoc, hfξ]
  exact isEtaleCompletion_of_forall_eq_inj (S.presheaf.stalk x) (ChartRing k m e) hAd hAn hRc ψ inferInstance hprim hfin
    (by rw [hdimR, hdimS]) hinj

end GlobalTheory.TautEtaleB
