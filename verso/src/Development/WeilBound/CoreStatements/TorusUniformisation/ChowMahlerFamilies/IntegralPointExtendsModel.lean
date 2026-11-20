import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.IntegralPointExtension

/- English proof (translation)
Use `letI : Algebra A B := ψ.hom.toAlgebra`. Use `letI : Field B := hB.toField`. Establish `hv : ValuativeCriterion.Existence sY` using `(IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper sY) : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) sY).1.1.1.existence`. Set `S : ValuativeCommSq sY` to `{ R := A, K := B, i₁ := φ, i₂ := t, commSq := ⟨h⟩ }`. Take `⟨⟨l⟩⟩` from `hv S`.

Conclude with `⟨l.l, l.fac_left, l.fac_right⟩`.
-/
theorem exists_lift {A B : CommRingCat.{0}} (ψ : A ⟶ B) [IsDomain A] [ValuationRing A] (hB : IsField B)
    (hf : letI := ψ.hom.toAlgebra; IsFractionRing A B) {Y S : Scheme.{0}} (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec B ⟶ Y) (t : Spec A ⟶ S) (h : φ ≫ sY = Spec.map ψ ≫ t) :
    ∃ m : Spec A ⟶ Y, Spec.map ψ ≫ m = φ ∧ m ≫ sY = t := by
  letI : Algebra A B := ψ.hom.toAlgebra
  letI : Field B := hB.toField
  have hv : ValuativeCriterion.Existence sY :=
    (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper sY) :
      (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) sY).1.1.1.existence
  let S : ValuativeCommSq sY :=
    { R := A, K := B, i₁ := φ, i₂ := t, commSq := ⟨h⟩ }
  obtain ⟨⟨l⟩⟩ := hv S
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/- English proof (translation)
Establish `hs : ∀ x : X, genericPoint X ⤳ x` using `fun x => (genericPoint_spec X).specializes trivial`. Establish `hlift : ∀ x : X, ∃ m : Spec (X.presheaf.stalk x) ⟶ Y, Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ m = φ ∧ m ≫ sY = X.fromSpecStalk x ≫ sX`. Introduce `x`. Use `haveI := hv x`. Use `letI : Algebra (X.presheaf.stalk x) X.functionField := (X.presheaf.stalkSpecializes (hs x)).hom.toAlgebra`.

Establish `hfr : IsFractionRing (X.presheaf.stalk x) X.functionField`. Use `(inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField) using 1` and compare the differences between its conclusion and the goal. Use `exists_lift (A := X.presheaf.stalk x) (B := X.functionField) (X.presheaf.stalkSpecializes (hs x)) (Field.toIsField _) hfr sY φ (X.fromSpecStalk x ≫ sX) ?_` and prove the remaining obligations. Rewrite using `[h, ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`. Use `choose m hm1 hm2 using hlift`.

Set `r0` to `Scheme.PartialMap.ofFromSpecStalk sX sY (x := genericPoint X) φ h`. Establish `hr0` using `Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (x := genericPoint X) φ h`. Establish `hdom : ∀ x : X, x ∈ r0.toRationalMap.domain`. Introduce `x`. Set `gx` to `Scheme.PartialMap.ofFromSpecStalk sX sY (m x) (hm2 x)`.

Establish `hx : x ∈ gx.domain` using `Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (m x) (hm2 x)`. Establish `hg : genericPoint X ∈ gx.domain` using `(hs x).mem_open gx.domain.2 hx`. Establish `key : gx.fromSpecStalkOfMem hg = φ`. Establish `e1 : gx.domain.fromSpecStalkOfMem (genericPoint X) hg = Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ gx.domain.fromSpecStalkOfMem x hx`. Rewrite using `[← cancel_mono gx.domain.ι]`.

Simplify using `[Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`. Establish `e2` using `Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (m x) (hm2 x)`. Express the relevant statement in the definitionally equal form `gx.domain.fromSpecStalkOfMem (genericPoint X) hg ≫ gx.hom = φ`. Rewrite using `[e1, Category.assoc]`. Express the relevant statement in the definitionally equal form `_ ≫ gx.fromSpecStalkOfMem hx = φ`.

Rewrite using `[e2, hm1]`. Rewrite using `[Scheme.RationalMap.mem_domain]`. Use `⟨gx, hx, Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_⟩` and prove the remaining obligations. Use `Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq (x := genericPoint X) gx r0 hg hr0 ?_` and prove the remaining obligations. Rewrite using `[key, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]`.

Set `P` to `r0.toRationalMap.toPartialMap`. Establish `htop : (⊤ : X.Opens) = P.domain`. Use `(top_le_iff.mp ?_).symm` and prove the remaining obligations. Introduce `x _`. Conclude with `hdom x`.

Use `⟨X.topIso.inv ≫ (X.isoOfEq htop).hom ≫ P.hom, ?_⟩` and prove the remaining obligations. Establish `hP : P.toRationalMap = r0.toRationalMap` using `Scheme.RationalMap.toRationalMap_toPartialMap _`. Establish `hgP : genericPoint X ∈ P.domain` using `hdom _`. Establish `hPeq : P.fromSpecStalkOfMem hgP = φ`. Establish `e4 : P.fromFunctionField = r0.fromFunctionField`.

Rewrite using `[← Scheme.RationalMap.fromFunctionField_toRationalMap, hP, Scheme.RationalMap.fromFunctionField_toRationalMap]`. Conclude with `e4.trans (Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (x := genericPoint X) φ h)`. Establish `e3 : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫ (X.isoOfEq htop).hom = P.domain.fromSpecStalkOfMem (genericPoint X) hgP`. Rewrite using `[← cancel_mono P.domain.ι]`. Simplify using `[Scheme.Opens.fromSpecStalkOfMem_ι]`.

Rewrite using `[← hPeq]`. Express the relevant statement in the definitionally equal form `_ = P.domain.fromSpecStalkOfMem (genericPoint X) hgP ≫ P.hom`. Rewrite using `[← e3]`. Simplify using `only [Category.assoc]`.
-/
theorem extend_functionField {X Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated]
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk _ ≫ sX) :
    ∃ g : X ⟶ Y, X.fromSpecStalk (genericPoint X) ≫ g = φ := by
  classical
  have hs : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hlift : ∀ x : X, ∃ m : Spec (X.presheaf.stalk x) ⟶ Y,
      Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ m = φ ∧ m ≫ sY = X.fromSpecStalk x ≫ sX := by
    intro x
    haveI := hv x
    letI : Algebra (X.presheaf.stalk x) X.functionField :=
      (X.presheaf.stalkSpecializes (hs x)).hom.toAlgebra
    have hfr : IsFractionRing (X.presheaf.stalk x) X.functionField := by
      convert (inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField) using 1
    refine exists_lift (A := X.presheaf.stalk x) (B := X.functionField)
      (X.presheaf.stalkSpecializes (hs x)) (Field.toIsField _) hfr sY φ (X.fromSpecStalk x ≫ sX) ?_
    rw [h, ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  choose m hm1 hm2 using hlift
  let r0 := Scheme.PartialMap.ofFromSpecStalk sX sY (x := genericPoint X) φ h
  have hr0 := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (x := genericPoint X) φ h
  have hdom : ∀ x : X, x ∈ r0.toRationalMap.domain := by
    intro x
    let gx := Scheme.PartialMap.ofFromSpecStalk sX sY (m x) (hm2 x)
    have hx : x ∈ gx.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (m x) (hm2 x)
    have hg : genericPoint X ∈ gx.domain := (hs x).mem_open gx.domain.2 hx
    have key : gx.fromSpecStalkOfMem hg = φ := by
      have e1 : gx.domain.fromSpecStalkOfMem (genericPoint X) hg =
          Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ gx.domain.fromSpecStalkOfMem x hx := by
        rw [← cancel_mono gx.domain.ι]
        simp [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      have e2 := Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (m x) (hm2 x)
      change gx.domain.fromSpecStalkOfMem (genericPoint X) hg ≫ gx.hom = φ
      rw [e1, Category.assoc]
      change _ ≫ gx.fromSpecStalkOfMem hx = φ
      rw [e2, hm1]
    rw [Scheme.RationalMap.mem_domain]
    refine ⟨gx, hx, Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_⟩
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq (x := genericPoint X) gx r0 hg hr0 ?_
    rw [key, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  let P := r0.toRationalMap.toPartialMap
  have htop : (⊤ : X.Opens) = P.domain := by
    refine (top_le_iff.mp ?_).symm
    intro x _
    exact hdom x
  refine ⟨X.topIso.inv ≫ (X.isoOfEq htop).hom ≫ P.hom, ?_⟩
  have hP : P.toRationalMap = r0.toRationalMap := Scheme.RationalMap.toRationalMap_toPartialMap _
  have hgP : genericPoint X ∈ P.domain := hdom _
  have hPeq : P.fromSpecStalkOfMem hgP = φ := by
    have e4 : P.fromFunctionField = r0.fromFunctionField := by
      rw [← Scheme.RationalMap.fromFunctionField_toRationalMap, hP,
        Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact e4.trans (Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (x := genericPoint X) φ h)
  have e3 : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫ (X.isoOfEq htop).hom =
      P.domain.fromSpecStalkOfMem (genericPoint X) hgP := by
    rw [← cancel_mono P.domain.ι]
    simp [Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [← hPeq]
  change _ = P.domain.fromSpecStalkOfMem (genericPoint X) hgP ≫ P.hom
  rw [← e3]
  simp only [Category.assoc]

/- English proof (translation)
Distinguish the cases in `h0 : p = ⊥`. Substitute `h0` using the available equality. Establish `hF : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R))`. Establish `h1` using `Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)`. Unfold `IsFractionRing`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Conclude with `Ideal.primeCompl_bot.symm`. Use `letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R`. Rewrite using `[ValuationRing.iff_dvd_total]`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `ha : a = 0`. Use `right`. Rewrite using `[ha]`. Conclude with `dvd_zero b`. Use the proof step `left; exact ⟨a⁻¹ * b, by rw [← _root_.mul_assoc, mul_inv_cancel₀ ha, _root_.one_mul]⟩`.

Use `haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 (Localization.AtPrime p) infer_instance`.
-/
private theorem valuationRing_localization_atPrime_dedekind (R : Type) [CommRing R] [IsDedekindDomain R] (p : Ideal R) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  by_cases h0 : p = ⊥
  · subst h0
    have hF : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
      have h1 := Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
      unfold IsFractionRing
      convert h1 using 1
      exact Ideal.primeCompl_bot.symm
    letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
    rw [ValuationRing.iff_dvd_total]
    refine ⟨fun a b => ?_⟩
    by_cases ha : a = 0
    · right; rw [ha]; exact dvd_zero b
    · left; exact ⟨a⁻¹ * b, by rw [← _root_.mul_assoc, mul_inv_cancel₀ ha, _root_.one_mul]⟩
  · haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 (Localization.AtPrime p)
    infer_instance

/- English proof (translation)
Use `haveI : (PrimeSpectrum.asIdeal (R := R) x).IsPrime := PrimeSpectrum.isPrime (R := R) x`. Establish `e` using `(Spec.stalkIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv`. Establish `hL` using `valuationRing_localization_atPrime_dedekind R (PrimeSpectrum.asIdeal (R := R) x)`. Rewrite `hL`, the goal using `[ValuationRing.iff_dvd_total]`. Use `⟨fun a b => (hL.total (e a) (e b)).imp (fun h => ?_) (fun h => ?_)⟩` and prove the remaining obligations.

Simplify using `using map_dvd e.symm h`. Simplify using `using map_dvd e.symm h`.
-/
theorem stalk_valuationRing (R : Type) [CommRing R] [IsDedekindDomain R] (x : Sp R) :
    ValuationRing ((Sp R).presheaf.stalk x) := by
  haveI : (PrimeSpectrum.asIdeal (R := R) x).IsPrime := PrimeSpectrum.isPrime (R := R) x
  have e := (Spec.stalkIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv
  have hL := valuationRing_localization_atPrime_dedekind R (PrimeSpectrum.asIdeal (R := R) x)
  rw [ValuationRing.iff_dvd_total] at hL ⊢
  refine ⟨fun a b => (hL.total (e a) (e b)).imp (fun h => ?_) (fun h => ?_)⟩
  · simpa using map_dvd e.symm h
  · simpa using map_dvd e.symm h

/- English proof (translation)
Use `haveI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)`. Use `letI : Algebra (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)`. Use `haveI : IsFractionRing (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField := functionField_isFractionRing_of_affine (CommRingCat.of R)`. Set `eK : (Spec (CommRingCat.of R)).functionField ≃ₐ[CommRingCat.of R] K` to `IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of R)) _ K`. Establish `hfs : (Sp R).fromSpecStalk (genericPoint (Sp R)) = Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField))`.

Rewrite using `[Spec.fromSpecStalk_eq']`. Both sides reduce to the same expression. Establish `hc1 : CommRingCat.ofHom (algebraMap R K) ≫ CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) = CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField)`. Use extensionality with `r`. Simplify using `[eK]`.

Establish `hc2 : CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField) ≫ CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) = CommRingCat.ofHom (algebraMap R K)`. Use extensionality with `r`. Simplify using `[eK]`. Establish `hc3 : CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) ≫ CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) = 𝟙 _`. Use extensionality with `r`.

Simplify using the standard rewrite rules. Establish `k1 : Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField))`. Rewrite using `[← hc1, Spec.map_comp]`. Establish `k3 : Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫ Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) = 𝟙 (Spec (CommRingCat.of K))`. Rewrite using `[← Spec.map_id, ← hc3, Spec.map_comp]`.

Set `φ : Spec (Spec (CommRingCat.of R)).functionField ⟶ Y` to `Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫ y`. Establish `h' : φ ≫ sY = (Sp R).fromSpecStalk _ ≫ sX` using `by show (Spec.map _ ≫ y) ≫ sY = _`. Rewrite using `[Category.assoc, h, spMap, hfs, ← Category.assoc]`. Conclude with `congrArg (· ≫ sX) k1`. Take `⟨g, hg⟩` from `extend_functionField (X := Sp R) (stalk_valuationRing R) sX sY φ h'`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `e1 : spMap (algebraMap R K) = Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫ (Sp R).fromSpecStalk (genericPoint (Sp R))`. Rewrite using `[hfs, spMap, ← Spec.map_comp, hc2]`. Rewrite using `[e1, Category.assoc, hg]`. Use `show Spec.map _ ≫ Spec.map _ ≫ y = y`.

Rewrite using `[← Category.assoc]`. Conclude with `(congrArg (· ≫ y) k3).trans (Category.id_comp y)`.
-/
theorem extend_dedekind (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Y S : Scheme.{0}} [Y.IsSeparated] (sX : Sp R ⟶ S) (sY : Y ⟶ S) [IsProper sY] (y : Sp K ⟶ Y)
    (h : y ≫ sY = spMap (algebraMap R K) ≫ sX) : ∃ g : Sp R ⟶ Y, spMap (algebraMap R K) ≫ g = y := by
  classical
  haveI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  letI : Algebra (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField :=
    instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
  haveI : IsFractionRing (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of R)
  let eK : (Spec (CommRingCat.of R)).functionField ≃ₐ[CommRingCat.of R] K :=
    IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of R)) _ K
  have hfs : (Sp R).fromSpecStalk (genericPoint (Sp R)) =
      Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField)) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  have hc1 : CommRingCat.ofHom (algebraMap R K) ≫
      CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) =
      CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField) := by
    ext r
    simp [eK]
  have hc2 : CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField) ≫
      CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) =
      CommRingCat.ofHom (algebraMap R K) := by
    ext r
    simp [eK]
  have hc3 : CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) ≫
      CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) = 𝟙 _ := by
    ext r
    simp
  have k1 : Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField)) := by
    rw [← hc1, Spec.map_comp]
  have k3 : Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫
      Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) =
      𝟙 (Spec (CommRingCat.of K)) := by
    rw [← Spec.map_id, ← hc3, Spec.map_comp]
  let φ : Spec (Spec (CommRingCat.of R)).functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫ y
  have h' : φ ≫ sY = (Sp R).fromSpecStalk _ ≫ sX := by
    show (Spec.map _ ≫ y) ≫ sY = _
    rw [Category.assoc, h, spMap, hfs, ← Category.assoc]
    exact congrArg (· ≫ sX) k1
  obtain ⟨g, hg⟩ := extend_functionField (X := Sp R) (stalk_valuationRing R) sX sY φ h'
  refine ⟨g, ?_⟩
  have e1 : spMap (algebraMap R K) =
      Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫
        (Sp R).fromSpecStalk (genericPoint (Sp R)) := by
    rw [hfs, spMap, ← Spec.map_comp, hc2]
  rw [e1, Category.assoc, hg]
  show Spec.map _ ≫ Spec.map _ ≫ y = y
  rw [← Category.assoc]
  exact (congrArg (· ≫ y) k3).trans (Category.id_comp y)

end PositivityTheory.Xgn.IntegralPointExtension

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c _ Y F _ _ f y hy`. Take `⟨N, i, hi, hs⟩` from `Y.proj`. Use `haveI : IsProper Y.s := by`. Rewrite using `[← hs]`. Use `haveI := isProper_str (𝓞 c.F) N`.

Use `infer_instance`. Use `haveI : Y.X.IsSeparated := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `e : terminal.from Y.X = Y.s ≫ terminal.from _` using `terminal.hom_ext _ _`. Rewrite using `[e]`.

Use `infer_instance`. Use `PositivityTheory.Xgn.IntegralPointExtension.extend_dedekind (𝓞 F) F (spMap (RingOfIntegers.mapRingHom f)) Y.s (y ≫ Y.j) ?_` and prove the remaining obligations. Establish `hj : Y.j ≫ Y.s = pullback.snd Xo.s _ ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Simplify using `only [Model.j, Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc, Y.jQ_over]`.

Rewrite using `[Category.assoc, hj, ← Category.assoc, hy]`. Simplify using `only [spMap, ← Spec.map_comp]`. Use `congr 1`.
-/
theorem PositivityTheory.Xgn.integral_point_extends_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c _ Y F _ _ f y hy
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI : IsProper Y.s := by
    rw [← hs]
    haveI := isProper_str (𝓞 c.F) N
    infer_instance
  haveI : Y.X.IsSeparated := by
    refine ⟨?_⟩
    have e : terminal.from Y.X = Y.s ≫ terminal.from _ := terminal.hom_ext _ _
    rw [e]
    infer_instance
  refine PositivityTheory.Xgn.IntegralPointExtension.extend_dedekind (𝓞 F) F
    (spMap (RingOfIntegers.mapRingHom f)) Y.s (y ≫ Y.j) ?_
  have hj : Y.j ≫ Y.s = pullback.snd Xo.s _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  rw [Category.assoc, hj, ← Category.assoc, hy]
  simp only [spMap, ← Spec.map_comp]
  congr 1
