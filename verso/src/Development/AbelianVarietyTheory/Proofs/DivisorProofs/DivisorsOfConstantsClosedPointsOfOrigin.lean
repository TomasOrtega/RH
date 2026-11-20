import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

/- English proof (translation)
Introduce `hKO`. Unfold `GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO`. Unfold `GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith`. Introduce `T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne`. Establish `hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X])` using `hne`.

Use `haveI hac : IsAlgClosed (ResidueField T) := (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1`. Take `⟨c, hc⟩` from `GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'`. Set `τ : T[X] ≃ₐ[T] T[X]` to `algEquivAevalXAddC (-c)`. Establish `hτX : τ X = X - C c` using `by simp [τ, sub_eq_add_neg]`. Establish `hτC : ∀ a : T, τ (C a) = C a` using `fun a => τ.commutes a`.

Set `P' : Ideal T[X]` to `P.comap (τ : T[X] →+* T[X])`. Use `haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _`. Establish `hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T`. Rewrite using `[← hPm]`. Use extensionality with `a`.

Simplify using `only [Ideal.mem_comap, P']`. Rewrite using `[show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]`. Establish `hXP' : (X : T[X]) ∈ P'`. Simplify using `only [P', Ideal.mem_comap]`. Rewrite using `[show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]`.

Conclude with `hc`. Establish `hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X}`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `p hp`. Establish `hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])}` using `Ideal.mem_span_singleton.2 X_dvd_sub_C`.

Establish `hc0 : C (p.coeff 0) ∈ P'`. Establish `h1 : p - C (p.coeff 0) ∈ P'`. Take `⟨u, hu⟩` from `(X_dvd_sub_C : X ∣ p - C (p.coeff 0))`. Rewrite using `[hu]`. Conclude with `P'.mul_mem_right _ hXP'`.

Use `P'.sub_mem hp h1` as an intermediate fact. Simplify using `using this`. Establish `hc0' : p.coeff 0 ∈ maximalIdeal T` using `by rw [← hP'C]; exact hc0`. Establish `: p = C (p.coeff 0) + (p - C (p.coeff 0))` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap, hP'C]`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hXP'`.

Set `f' : T[X] →+* O` to `(algebraMap T[X] O).comp (τ : T[X] →+* T[X])`. Set `alg' : Algebra T[X] O` to `f'.toAlgebra`. Establish `tower' : @IsScalarTower T T[X] O _ alg'.toSMul _`. Use `@IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_` and prove the remaining obligations. Introduce `x`.

Express the relevant statement in the definitionally equal form `algebraMap T O x = f' (algebraMap T T[X] x)`. Simplify using `only [f', RingHom.comp_apply]`. Rewrite using `[show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x, ← IsScalarTower.algebraMap_apply]`. Establish `hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl`. Use extensionality with `x`.

Rewrite using `[Submonoid.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`.

Use `⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P`. Establish `hx' : x ∉ P` using `hx`. Use `hx' using 2` and compare the differences between its conclusion and the goal. Conclude with `(τ : T[X] ≃+* T[X]).apply_symm_apply x`.

Set `Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P` to `IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap`. Set `φ' : Localization.AtPrime P' →+* O` to `φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)`. Establish `hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f'`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [φ', f', RingHom.comp_apply]`.

Rewrite using `[show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x) = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from IsLocalization.ringEquivOfRingEquiv_eq _ x]`. Rewrite using `[← RingHom.comp_apply φ, hφ]`. Both sides reduce to the same expression. Establish `hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ'`. Take `⟨h1, h2, h3, h4⟩` from `hsh`.

Use `⟨h1, h2, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := h3 haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) := ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩`. Conclude with `RingHom.isLocalHom_comp _ _`. Establish `: (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso` using `RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso`. Establish `h5` using `CategoryTheory.MorphismProperty.RespectsIso.precomp (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale)) Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Conclude with `@hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'`.
-/
theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
