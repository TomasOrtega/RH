import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

open GlobalTheory.LocAcyc in
open CategoryTheory in

/- English proof (translation)
Introduce `hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH`. Use `set p : Ideal T := P.comap (C : T →+* T[X]) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Set `T'` to `Localization.AtPrime p`. Establish `hle : p.primeCompl ≤ nonZeroDivisors T` using `p.primeCompl_le_nonZeroDivisors`.

Establish `hAIC' : AbsIntClosed T'` using `((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl (fun h => h (zero_mem p))).2`. Establish `hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a)` using `fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]`. Establish `hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s)`. Introduce `s`.

Establish `hs : C (s : T) ∈ P.primeCompl` using `s.2`. Establish `hu` using `(IsLocalization.map_units (Localization.AtPrime P) (⟨C (s : T), hs⟩ : P.primeCompl)).map φ`. Rewrite `hu` using `[← RingHom.comp_apply, hφ]`. Rewrite using `[hTO]` and apply the resulting hypothesis. Use `letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra`.

Use `haveI : IsScalarTower T T' O := IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)`. Use `letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra`. Use `haveI : IsScalarTower T' T'[X] O := IsScalarTower.of_algebraMap_eq (fun x => by`. Express the relevant statement in the definitionally equal form `_ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)`. Rewrite using `[Polynomial.algebraMap_eq, eval₂_C])`.

Use `letI : Algebra T[X] T'[X] := Polynomial.algebra T T'`. Use `haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] := Polynomial.isLocalization p.primeCompl T'`. Establish `hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X])`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨s, hs, rfl⟩ hsP`.

Conclude with `hs hsP`. Use `set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'`. Use `haveI hP'prime : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj`. Establish `hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P` using `IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj`. Establish `hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a)` using `fun a => by`.

Express the relevant statement in the definitionally equal form `_ = (C a).map (algebraMap T T')`. Rewrite using `[Polynomial.map_C]`. Establish `hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T'`. Rewrite using `[← IsLocalization.map_comap p.primeCompl T' (P'.comap C), ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'), IsLocalization.AtPrime.comap_maximalIdeal T' p]`. Use `congr 1`.

Use extensionality with `a`. Express the relevant statement in the definitionally equal form `C (algebraMap T T' a) ∈ P' ↔ C a ∈ P`. Rewrite using `[hCcomm, ← Ideal.mem_comap, hcomapP']`. Use `haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by`. Use `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'` as an intermediate fact.

Establish `hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl`. Use extensionality with `x`. Simplify using `only [Ideal.mem_primeCompl_iff, hcomapP']`. Unfold `IsLocalization.AtPrime at this ⊢`. Rewrite `this` using `[hc]`.

Conclude with `this`. Set `e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P'` to `IsLocalization.algEquiv P.primeCompl _ _`. Set `φ' : Localization.AtPrime P' →+* O` to `φ.comp e.symm.toRingEquiv.toRingHom`. Establish `hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O`. Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _`. Rewrite using `[Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]`. Express the relevant statement in the definitionally equal form `eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _`. Rewrite using `[Polynomial.map_X, eval₂_X]`. Establish `hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O`.

Use `IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]`. Use `RingHom.ext fun f => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (e.symm (algebraMap T[X] _ f)) = _`. Rewrite using `[AlgEquiv.commutes, ← RingHom.comp_apply, hφ]`.

Establish `hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ'`. Take `⟨h1, h2, h3, h4⟩` from `hSH`. Use `⟨h1, h2, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsUnit (φ (e.symm a)) at ha`.

Establish `h5 : IsUnit (e.symm a)` using `h3.map_nonunit _ ha`. Simplify using `using h5.map e`. Use `haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢`. Rewrite using `[CommRingCat.ofHom_comp]`.

Use `haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) := inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)`. Conclude with `(MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4`. Establish `key : DivConst T' O` using `hL T' O hAIC' P' φ' hφ' hSH' hmax trivial`. Establish `hinj : Function.Injective (algebraMap T T')` using `IsLocalization.injective T' hle`. Introduce `b c s hs hbc`.

Establish `hs' : algebraMap T T' s ≠ 0` using `fun h => hs (hinj (by rw [h, map_zero]))`. Rewrite `hbc` using `[IsScalarTower.algebraMap_apply T T' O]`. Take `⟨a', w, hb⟩` from `key b c _ hs' hbc`. Take `⟨⟨a, u⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl a'`. Take `⟨v, hv⟩` from `hunit u`.

Use `⟨a, v⁻¹ * w, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, Units.val_mul, ← mul_assoc]`. Use `congr 1`. Rewrite using `[Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a, IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]`.
-/
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
