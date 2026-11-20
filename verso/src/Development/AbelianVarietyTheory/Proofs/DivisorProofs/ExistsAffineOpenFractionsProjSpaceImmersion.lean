import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersion
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjSpace

/- English proof (translation)
Substitute `hA hB` using the available equality. Conclude with `id`.
-/
theorem surjective_appLE_of_eq {X Z : Scheme.{0}} {f : Z ⟶ X} {A A' : X.Opens} {B B' : Z.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ f ⁻¹ᵁ A) (h' : B' ≤ f ⁻¹ᵁ A') :
    Function.Surjective (f.appLE A B h).hom → Function.Surjective (f.appLE A' B' h').hom := by
  subst hA hB
  exact id

/- English proof (translation)
Introduce `R _ N Y φ hφ y V i hyV hyi`. Take `⟨U', hU', hU⟩` from `φ.isEmbedding.isInducing.isOpen_iff.1 V.isOpen`. Set `O : (PSpace R N).Opens` to `⟨U', hU'⟩ ⊓ φ.coborderRange`. Establish `hyO : φ y ∈ O` using `⟨show φ y ∈ U' by rw [← Set.mem_preimage, hU]; exact hyV, subset_coborder ⟨y, rfl⟩⟩`. Take `⟨h, hhO, hyh⟩` from `(isAffineOpen_chart R N i).exists_basicOpen_le (V := O) ⟨φ y, hyO⟩ hyi`.

Establish `hD : IsAffineOpen ((PSpace R N).basicOpen h)` using `(isAffineOpen_chart R N i).basicOpen h`. Establish `hDc : (PSpace R N).basicOpen h ≤ chart R N i` using `(PSpace R N).basicOpen_le h`. Establish `hle : (PSpace R N).basicOpen h ≤ φ.coborderRange` using `fun z hz => (hhO hz).2`. Use `haveI : IsAffine ((PSpace R N).basicOpen h) := hD`. Establish `hp : IsPullback (φ ∣_ (PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h).ι ((PSpace R N).homOfLE hle) φ.liftCoborder`.

Use `IsPullback.of_bot (h₃₁ := φ) (v₂₁ := 𝟙 _) (v₂₂ := φ.coborderRange.ι) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.comp_id, Scheme.homOfLE_ι]`. Conclude with `isPullback_morphismRestrict φ _`. Rewrite using `[← cancel_mono φ.coborderRange.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.liftCoborder_ι, morphismRestrict_ι]`. Conclude with `IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Scheme.Hom.liftCoborder_ι]⟩`.

Use `haveI : IsClosedImmersion (φ ∣_ (PSpace R N).basicOpen h) := MorphismProperty.of_isPullback hp.flip inferInstance`. Take `⟨hWa, hsurj0⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine (φ ∣_ (PSpace R N).basicOpen h)`. Establish `hsurj : Function.Surjective (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom`. Rewrite `hsurj0` using `[Scheme.Hom.appTop, morphismRestrict_app']`. Conclude with `surjective_appLE_of_eq (by simp) (by simp) _ _ hsurj0`.

Establish `hWc : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ φ ⁻¹ᵁ chart R N i` using `φ.preimage_mono hDc`. Use `⟨φ ⁻¹ᵁ (PSpace R N).basicOpen h, hWc, hyh, ?_, hWa, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `: φ z ∈ U'` using `(hhO hz).1`. Rewrite `this` using `[← Set.mem_preimage, hU]`.

Conclude with `this`. Introduce `g`. Take `⟨a, rfl⟩` from `hsurj g`. Establish `hloc` using `(isAffineOpen_chart R N i).isLocalization_basicOpen h`. Establish `key : ∀ p : MvPolynomial (Fin (N + 1)) R, (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom (algebraMap Γ(PSpace R N, chart R N i) Γ(PSpace R N, (PSpace R N).basicOpen h) (MvPolynomial.aeval (R` using `R) (ratio R N i) p)) = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) _).hom (pullRatio φ _ i hWc) p := by`.

Introduce `p`. Establish `e1` using `appLE_resG φ hDc (le_rfl : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ _) (MvPolynomial.aeval (R := R) (ratio R N i) p)`. Establish `e2` using `congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ (PSpace R N).basicOpen h) (i := i) (hi := hWc))`. Conclude with `e1.trans e2`. Take `⟨⟨b, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers h) a`.

Take `⟨m, hm⟩` from `s.2`. Take `⟨P, rfl⟩` from `aeval_ratio_surjective R N i b`. Take `⟨h₀, hh₀⟩` from `aeval_ratio_surjective R N i h`. Establish `hQ : MvPolynomial.aeval (R` using `R) (ratio R N i) (h₀ ^ m) = (s : Γ(PSpace R N, chart R N i)) := by`. Rewrite using `[map_pow, hh₀, ← hm]`.

Use `⟨P, h₀ ^ m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← key, hQ]`. Conclude with `(IsLocalization.map_units _ s).map _`. Rewrite using `[← key, ← key, hQ, ← map_mul]`. Conclude with `congrArg _ hs`.
-/
theorem exists_affineOpen_fraction_pullRatio : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  intro R _ N Y φ hφ y V i hyV hyi
  obtain ⟨U', hU', hU⟩ := φ.isEmbedding.isInducing.isOpen_iff.1 V.isOpen
  let O : (PSpace R N).Opens := ⟨U', hU'⟩ ⊓ φ.coborderRange
  have hyO : φ y ∈ O := ⟨show φ y ∈ U' by rw [← Set.mem_preimage, hU]; exact hyV, subset_coborder ⟨y, rfl⟩⟩
  obtain ⟨h, hhO, hyh⟩ := (isAffineOpen_chart R N i).exists_basicOpen_le (V := O) ⟨φ y, hyO⟩ hyi
  have hD : IsAffineOpen ((PSpace R N).basicOpen h) := (isAffineOpen_chart R N i).basicOpen h
  have hDc : (PSpace R N).basicOpen h ≤ chart R N i := (PSpace R N).basicOpen_le h
  have hle : (PSpace R N).basicOpen h ≤ φ.coborderRange := fun z hz => (hhO hz).2
  haveI : IsAffine ((PSpace R N).basicOpen h) := hD
  have hp : IsPullback (φ ∣_ (PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h).ι
      ((PSpace R N).homOfLE hle) φ.liftCoborder := by
    refine IsPullback.of_bot (h₃₁ := φ) (v₂₁ := 𝟙 _) (v₂₂ := φ.coborderRange.ι) ?_ ?_ ?_
    · rw [Category.comp_id, Scheme.homOfLE_ι]
      exact isPullback_morphismRestrict φ _
    · rw [← cancel_mono φ.coborderRange.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Hom.liftCoborder_ι, morphismRestrict_ι]
    · exact IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Scheme.Hom.liftCoborder_ι]⟩
  haveI : IsClosedImmersion (φ ∣_ (PSpace R N).basicOpen h) := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨hWa, hsurj0⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (φ ∣_ (PSpace R N).basicOpen h)
  have hsurj : Function.Surjective
      (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom := by
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at hsurj0
    exact surjective_appLE_of_eq (by simp) (by simp) _ _ hsurj0
  have hWc : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ φ ⁻¹ᵁ chart R N i := φ.preimage_mono hDc
  refine ⟨φ ⁻¹ᵁ (PSpace R N).basicOpen h, hWc, hyh, ?_, hWa, ?_⟩
  · intro z hz
    have : φ z ∈ U' := (hhO hz).1
    rw [← Set.mem_preimage, hU] at this
    exact this
  · intro g
    obtain ⟨a, rfl⟩ := hsurj g
    have hloc := (isAffineOpen_chart R N i).isLocalization_basicOpen h
    have key : ∀ p : MvPolynomial (Fin (N + 1)) R,
        (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom
          (algebraMap Γ(PSpace R N, chart R N i) Γ(PSpace R N, (PSpace R N).basicOpen h)
            (MvPolynomial.aeval (R := R) (ratio R N i) p)) =
        MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) _).hom
          (pullRatio φ _ i hWc) p := by
      intro p
      have e1 := appLE_resG φ hDc (le_rfl : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ _) (MvPolynomial.aeval (R := R) (ratio R N i) p)
      have e2 := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ (PSpace R N).basicOpen h) (i := i) (hi := hWc))
      exact e1.trans e2
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a
    obtain ⟨m, hm⟩ := s.2
    obtain ⟨P, rfl⟩ := aeval_ratio_surjective R N i b
    obtain ⟨h₀, hh₀⟩ := aeval_ratio_surjective R N i h
    have hQ : MvPolynomial.aeval (R := R) (ratio R N i) (h₀ ^ m) = (s : Γ(PSpace R N, chart R N i)) := by
      rw [map_pow, hh₀, ← hm]
    refine ⟨P, h₀ ^ m, ?_, ?_⟩
    · rw [← key, hQ]
      exact (IsLocalization.map_units _ s).map _
    · rw [← key, ← key, hQ, ← map_mul]
      exact congrArg _ hs

end GlobalTheory.ProjSpace
