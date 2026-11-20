import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

/- English proof (translation)
Take `⟨U, g, hxU, hg, hJ⟩` from `h`. Establish `hU : IsAffineOpen U.1` using `U.2`. Establish `hV : IsAffineOpen (f ''ᵁ U.1)` using `hU.image_of_isOpenImmersion f`. Use `⟨⟨f ''ᵁ U.1, hV⟩, (f.appIso U.1).inv.hom g, ⟨x, hxU, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ringEquiv_mem_nonZeroDivisors (f.appIso U.1).symm.commRingCatIsoToRingEquiv hg`.

Rewrite `hJ` using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]`. Establish `hs : Function.Surjective (f.appIso U.1).inv.hom` using `(f.appIso U.1).symm.commRingCatIsoToRingEquiv.surjective`. Rewrite using `[← Ideal.map_comap_of_surjective _ hs (J.ideal ⟨f ''ᵁ U.1, hV⟩), hJ, Ideal.map_span, Set.image_singleton]`.
-/
theorem cartAt_of_cartAt_comap {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt (J.comap f) x) : CartAt J (f x) := by
  obtain ⟨U, g, hxU, hg, hJ⟩ := h
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen (f ''ᵁ U.1) := hU.image_of_isOpenImmersion f
  refine ⟨⟨f ''ᵁ U.1, hV⟩, (f.appIso U.1).inv.hom g, ⟨x, hxU, rfl⟩, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors (f.appIso U.1).symm.commRingCatIsoToRingEquiv hg
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hJ
    have hs : Function.Surjective (f.appIso U.1).inv.hom :=
      (f.appIso U.1).symm.commRingCatIsoToRingEquiv.surjective
    rw [← Ideal.map_comap_of_surjective _ hs (J.ideal ⟨f ''ᵁ U.1, hV⟩), hJ, Ideal.map_span,
      Set.image_singleton]

/- English proof (translation)
Establish `e : (homOfLE h1 ≫ homOfLE h2 : A ⟶ A) = 𝟙 A` using `Subsingleton.elim _ _`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]`.
-/
private theorem res_res_lemma {Y : Scheme.{0}} {A B : Y.Opens} (h1 : A ≤ B) (h2 : B ≤ A)
    (y : Γ(Y, A)) :
    (Y.presheaf.map (homOfLE h1).op).hom ((Y.presheaf.map (homOfLE h2).op).hom y) = y := by
  have e : (homOfLE h1 ≫ homOfLE h2 : A ⟶ A) = 𝟙 A := Subsingleton.elim _ _
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, e, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]

/- English proof (translation)
Take `⟨V, g, hfx, hg, hJ⟩` from `h`. Establish `hV : IsAffineOpen V.1` using `V.2`. Take `⟨h0, hle, hx0⟩` from `hV.exists_basicOpen_le (V := f.opensRange) ⟨f x, x, rfl⟩ hfx`. Establish `hU : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen h0)` using `(hV.basicOpen h0).preimage_of_isOpenImmersion f hle`. Establish `hW : IsAffineOpen (f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0)` using `hU.image_of_isOpenImmersion f`.

Establish `heq : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 = Y.basicOpen h0`. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]`. Establish `hWD : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 ≤ Y.basicOpen h0` using `heq.le`. Establish `hDW : Y.basicOpen h0 ≤ f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0` using `heq.ge`. Set `r : Γ(Y, Y.basicOpen h0)` to `(Y.presheaf.map (homOfLE (Y.basicOpen_le h0)).op).hom g`.

Establish `hJD : J.ideal (Y.affineBasicOpen h0) = Ideal.span {r}`. Rewrite using `[← J.map_ideal_basicOpen V h0, hJ, Ideal.map_span, Set.image_singleton]`. Establish `hr : r ∈ nonZeroDivisors Γ(Y, Y.basicOpen h0)` using `by haveI := hV.isLocalization_basicOpen h0`. Conclude with `algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers h0) hg`. Set `s : Γ(Y, Y.basicOpen h0) →+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0)` to `(Y.presheaf.map (homOfLE hWD).op).hom`.

Set `s' : Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) →+* Γ(Y, Y.basicOpen h0)` to `(Y.presheaf.map (homOfLE hDW).op).hom`. Establish `ss' : ∀ y, s (s' y) = y` using `fun y => res_res_lemma hWD hDW y`. Establish `s's : ∀ y, s' (s y) = y` using `fun y => res_res_lemma hDW hWD y`. Set `σ : Γ(Y, Y.basicOpen h0) ≃+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0)` to `RingEquiv.ofRingHom s s' (RingHom.ext fun y => ss' y) (RingHom.ext fun y => s's y)`. Establish `hJW : J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ = Ideal.span {σ r}`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Establish `h3 : s' y ∈ J.ideal (Y.affineBasicOpen h0)` using `J.ideal_le_comap_ideal (U := Y.affineBasicOpen h0) (V := ⟨_, hW⟩) hDW hy`. Rewrite `h3` using `[hJD]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton.1 h3`.

Rewrite using `[Ideal.mem_span_singleton, ← ss' y, ha, map_mul]`. Conclude with `dvd_mul_right _ _`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Establish `h4 : r ∈ J.ideal (Y.affineBasicOpen h0)`. Rewrite using `[hJD]`.

Conclude with `Ideal.mem_span_singleton_self r`. Conclude with `J.ideal_le_comap_ideal (U := ⟨_, hW⟩) (V := Y.affineBasicOpen h0) hWD h4`. Set `ρ` to `(f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).commRingCatIsoToRingEquiv`. Use `⟨⟨f ⁻¹ᵁ Y.basicOpen h0, hU⟩, ρ (σ r), hx0, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ringEquiv_mem_nonZeroDivisors ρ (ringEquiv_mem_nonZeroDivisors σ hr)`.

Rewrite using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]`. Use extensionality with `y`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Establish `key : (f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).inv.hom y ∈ J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ ↔ σ r ∣ ρ.symm y`. Rewrite using `[hJW, Ideal.mem_span_singleton]`.

Both sides reduce to the same expression. Use `key.trans ?_` and prove the remaining obligations. Use `conv_rhs => rw [← ρ.apply_symm_apply y]`. Rewrite using `[map_dvd_iff]`.
-/
theorem cartAt_comap_of_cartAt {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt J (f x)) : CartAt (J.comap f) x := by
  obtain ⟨V, g, hfx, hg, hJ⟩ := h
  have hV : IsAffineOpen V.1 := V.2
  obtain ⟨h0, hle, hx0⟩ := hV.exists_basicOpen_le (V := f.opensRange) ⟨f x, x, rfl⟩ hfx
  have hU : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen h0) :=
    (hV.basicOpen h0).preimage_of_isOpenImmersion f hle
  have hW : IsAffineOpen (f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) := hU.image_of_isOpenImmersion f
  have heq : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 = Y.basicOpen h0 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
  have hWD : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 ≤ Y.basicOpen h0 := heq.le
  have hDW : Y.basicOpen h0 ≤ f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 := heq.ge
  let r : Γ(Y, Y.basicOpen h0) := (Y.presheaf.map (homOfLE (Y.basicOpen_le h0)).op).hom g
  have hJD : J.ideal (Y.affineBasicOpen h0) = Ideal.span {r} := by
    rw [← J.map_ideal_basicOpen V h0, hJ, Ideal.map_span, Set.image_singleton]
  have hr : r ∈ nonZeroDivisors Γ(Y, Y.basicOpen h0) := by
    haveI := hV.isLocalization_basicOpen h0
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers h0) hg
  let s : Γ(Y, Y.basicOpen h0) →+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) :=
    (Y.presheaf.map (homOfLE hWD).op).hom
  let s' : Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) →+* Γ(Y, Y.basicOpen h0) :=
    (Y.presheaf.map (homOfLE hDW).op).hom
  have ss' : ∀ y, s (s' y) = y := fun y => res_res_lemma hWD hDW y
  have s's : ∀ y, s' (s y) = y := fun y => res_res_lemma hDW hWD y
  let σ : Γ(Y, Y.basicOpen h0) ≃+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) :=
    RingEquiv.ofRingHom s s' (RingHom.ext fun y => ss' y) (RingHom.ext fun y => s's y)
  have hJW : J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ = Ideal.span {σ r} := by
    apply le_antisymm
    · intro y hy
      have h3 : s' y ∈ J.ideal (Y.affineBasicOpen h0) :=
        J.ideal_le_comap_ideal (U := Y.affineBasicOpen h0) (V := ⟨_, hW⟩) hDW hy
      rw [hJD] at h3
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 h3
      rw [Ideal.mem_span_singleton, ← ss' y, ha, map_mul]
      exact dvd_mul_right _ _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h4 : r ∈ J.ideal (Y.affineBasicOpen h0) := by
        rw [hJD]
        exact Ideal.mem_span_singleton_self r
      exact J.ideal_le_comap_ideal (U := ⟨_, hW⟩) (V := Y.affineBasicOpen h0) hWD h4
  let ρ := (f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).commRingCatIsoToRingEquiv
  refine ⟨⟨f ⁻¹ᵁ Y.basicOpen h0, hU⟩, ρ (σ r), hx0, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors ρ (ringEquiv_mem_nonZeroDivisors σ hr)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    ext y
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have key : (f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).inv.hom y ∈
        J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ ↔ σ r ∣ ρ.symm y := by
      rw [hJW, Ideal.mem_span_singleton]
      rfl
    refine key.trans ?_
    conv_rhs => rw [← ρ.apply_symm_apply y]
    rw [map_dvd_iff]

/- English proof (translation)
Introduce `X J O`. Rewrite using `[effCartier_iff_forall_cartAt]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `cartAt_of_cartAt_comap J O.ι ⟨x, hx⟩ (h ⟨x, hx⟩)`.

Introduce `h x`. Conclude with `cartAt_comap_of_cartAt J O.ι x (h x.1 x.2)`.
-/
theorem effCartier_comap_opens_iff : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens),
    FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  intro X J O
  rw [effCartier_iff_forall_cartAt]
  constructor
  · intro h x hx
    exact cartAt_of_cartAt_comap J O.ι ⟨x, hx⟩ (h ⟨x, hx⟩)
  · intro h x
    exact cartAt_comap_of_cartAt J O.ι x (h x.1 x.2)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
