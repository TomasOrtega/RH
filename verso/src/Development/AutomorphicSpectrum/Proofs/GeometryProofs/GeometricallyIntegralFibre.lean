import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralOfClosedFibre
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open IsLocalRing GlobalTheory.ProperFunctions

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x hx`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx`. Establish `hx' : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ ⊤ x trivial 0`. Rewrite using `[hx, map_zero]`.

Take `⟨W, hxW, iU, iV, h⟩` from `TopCat.Presheaf.germ_eq X.presheaf (U := ⊤) (V := ⊤) x trivial trivial f 0 hx'`. Use `Filter.mem_of_superset (W.2.mem_nhds hxW) fun y hy ↦ ?_` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]`. Rewrite using `[← X.presheaf.germ_res_apply iU y hy, h, map_zero, map_zero]`.
-/
theorem isClosed_germ_ne_zero (X : Scheme.{0}) (f : Γ(X, ⊤)) :
    IsClosed {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx
  have hx' : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ ⊤ x trivial 0 := by
    rw [hx, map_zero]
  obtain ⟨W, hxW, iU, iV, h⟩ := TopCat.Presheaf.germ_eq X.presheaf (U := ⊤) (V := ⊤) x trivial trivial f 0 hx'
  refine Filter.mem_of_superset (W.2.mem_nhds hxW) fun y hy ↦ ?_
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [← X.presheaf.germ_res_apply iU y hy, h, map_zero, map_zero]

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Establish `h1` using `(X.mem_basicOpen (U := ⊤) _ x trivial).mpr hu`. Establish `h2 : x ∈ p ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a)`. Rewrite using `[Scheme.preimage_basicOpen]`.

Conclude with `h1`. Establish `h3 : p x ∈ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a)` using `h2`. Rewrite `h3` using `[basicOpen_eq_of_affine, hx]`. Conclude with `h3 ha`.
-/
theorem germ_mem_maximalIdeal {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (x : X) (hx : p x = closedPoint A) {a : A} (ha : a ∈ maximalIdeal A) :
    X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) ∈
      maximalIdeal (X.presheaf.stalk x) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := (X.mem_basicOpen (U := ⊤) _ x trivial).mpr hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1
  have h3 : p x ∈ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact h3 ha

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian p`. Assume the negation of the conclusion as `hf`. Establish `hne : ∃ z : X, X.presheaf.germ ⊤ z trivial f ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Use `hf (TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x _ ↦ ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `hall x`. Take `⟨z, hz⟩` from `hne`. Establish `hcl` using `p.isClosedMap _ (isClosed_germ_ne_zero X f)`.

Establish `hmem : closedPoint A ∈ p '' {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0}` using `(specializes_closedPoint (p z)).mem_closed hcl ⟨z, hz, rfl⟩`. Take `⟨x, hxZ, hx⟩` from `hmem`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `hxZ ?_` and prove the remaining obligations. Establish `hθ : ∀ a : A, X.presheaf.germ U x hxU (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) = X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a))`.

Introduce `a`. Establish `e1 : p.appLE ⊤ U (le_preimage_top p _) = p.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op` using `rfl`. Rewrite using `[e1, CommRingCat.comp_apply]`. Conclude with `X.presheaf.germ_res_apply _ x hxU _`. Establish `hpow : ∀ n : ℕ, X.presheaf.germ ⊤ x trivial f ∈ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)`.

Introduce `n`. Establish `h1` using `Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom (h n ⟨U, hU⟩)`. Rewrite `h1` using `[Ideal.map_map, Ideal.map_map, Ideal.map_pow]`. Establish `h2 : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ U x hxU (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)` using `(X.presheaf.germ_res_apply _ x hxU f).symm`. Rewrite using `[h2]`.

Use `Ideal.pow_right_mono ?_ _ h1` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `X.presheaf.germ U x hxU (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) ∈ _`.

Rewrite using `[hθ]`. Conclude with `germ_mem_maximalIdeal p x hx ha`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x)) Ideal.IsPrime.ne_top'`. Establish `: X.presheaf.germ ⊤ x trivial f ∈ (⊥ : Ideal (X.presheaf.stalk x))`. Rewrite using `[← hbot, Ideal.mem_iInf]`.

Introduce `i`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ i) (hpow i)`. Simplify using `using this`.
-/
theorem eq_zero_of_mem_pow {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{0}} (p : X ⟶ Sp A) [UniversallyClosed p] [LocallyOfFiniteType p]
    (f : Γ(X, ⊤))
    (h : ∀ (n : ℕ) (U : X.affineOpens), X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f ∈
      (((maximalIdeal A) ^ (n + 1)).map (Scheme.ΓSpecIso (.of A)).inv.hom).map
        (p.appLE ⊤ U.1 (le_preimage_top p _)).hom) : f = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hf
  have hne : ∃ z : X, X.presheaf.germ ⊤ z trivial f ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hf (TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x _ ↦ ?_)
    rw [map_zero]
    exact hall x
  obtain ⟨z, hz⟩ := hne
  have hcl := p.isClosedMap _ (isClosed_germ_ne_zero X f)
  have hmem : closedPoint A ∈ p '' {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} :=
    (specializes_closedPoint (p z)).mem_closed hcl ⟨z, hz, rfl⟩
  obtain ⟨x, hxZ, hx⟩ := hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine hxZ ?_
  have hθ : ∀ a : A, X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    intro a
    have e1 : p.appLE ⊤ U (le_preimage_top p _) =
        p.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := rfl
    rw [e1, CommRingCat.comp_apply]
    exact X.presheaf.germ_res_apply _ x hxU _
  have hpow : ∀ n : ℕ, X.presheaf.germ ⊤ x trivial f ∈
      maximalIdeal (X.presheaf.stalk x) ^ (n + 1) := by
    intro n
    have h1 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom (h n ⟨U, hU⟩)
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_pow] at h1
    have h2 : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ U x hxU
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) :=
      (X.presheaf.germ_res_apply _ x hxU f).symm
    rw [h2]
    refine Ideal.pow_right_mono ?_ _ h1
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) ∈ _
    rw [hθ]
    exact germ_mem_maximalIdeal p x hx ha
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
    Ideal.IsPrime.ne_top'
  have : X.presheaf.germ ⊤ x trivial f ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
    rw [← hbot, Ideal.mem_iInf]
    intro i
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hpow i)
  simpa using this

/- English proof (translation)
Set `φ : ResidueField A →+* ResidueField B` to `ResidueField.map π`. Establish `hφ : Function.Bijective φ`. Use `⟨φ.injective, fun y ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `residue_surjective y`. Take `⟨a, rfl⟩` from `hπ b`.

Conclude with `⟨residue A a, ResidueField.map_residue π a⟩`. Establish `: IsIso (CommRingCat.ofHom φ)` using `(ConcreteCategory.isIso_iff_bijective _).mpr hφ`. Establish `: IsIso (spMap φ)` using `inferInstanceAs (IsIso (Spec.map _))`. Establish `e1 : φ.comp (residue A) = (residue B).comp π`. Use extensionality with `a`.

Conclude with `ResidueField.map_residue π a`. Establish `hw : spMap (residue B) ≫ spMap π = spMap φ ≫ spMap (residue A)`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]`. Establish `H` using `(IsPullback.of_hasPullback (pullback.snd p (spMap π)) (spMap (residue B))).paste_horiz (IsPullback.of_hasPullback p (spMap π))`. Rewrite `H` using `[hw]`.

Establish `R` using `IsPullback.of_hasPullback p (spMap (residue A))`. Establish `w : (pullback.fst (pullback.snd p (spMap π)) (spMap (residue B)) ≫ pullback.fst p (spMap π)) ≫ p = (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)) ≫ spMap φ) ≫ spMap (residue A)` using `H.w.trans (Category.assoc _ _ _).symm`. Establish `H2 : IsPullback (R.lift _ _ w) (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B))) (pullback.snd p (spMap (residue A))) (spMap φ)`. Use `IsPullback.of_right (h₁₂ := pullback.fst p (spMap (residue A))) (v₁₃ := p) (h₂₂ := spMap (residue A)) ?_ (R.lift_snd _ _ w) R` and prove the remaining obligations. Rewrite using `[R.lift_fst]`.

Conclude with `H`. Conclude with `MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H2 hG`.
-/
theorem geometricallyIntegral_fibre {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A)))) :
    GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B))) := by
  let φ : ResidueField A →+* ResidueField B := ResidueField.map π
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨residue A a, ResidueField.map_residue π a⟩
  have : IsIso (CommRingCat.ofHom φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (spMap φ) := inferInstanceAs (IsIso (Spec.map _))
  have e1 : φ.comp (residue A) = (residue B).comp π := by
    ext a
    exact ResidueField.map_residue π a
  have hw : spMap (residue B) ≫ spMap π = spMap φ ≫ spMap (residue A) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  have H := (IsPullback.of_hasPullback (pullback.snd p (spMap π)) (spMap (residue B))).paste_horiz
    (IsPullback.of_hasPullback p (spMap π))
  rw [hw] at H
  have R := IsPullback.of_hasPullback p (spMap (residue A))
  have w : (pullback.fst (pullback.snd p (spMap π)) (spMap (residue B)) ≫
      pullback.fst p (spMap π)) ≫ p =
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)) ≫ spMap φ) ≫
        spMap (residue A) := H.w.trans (Category.assoc _ _ _).symm
  have H2 : IsPullback (R.lift _ _ w) (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)))
      (pullback.snd p (spMap (residue A))) (spMap φ) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (spMap (residue A))) (v₁₃ := p)
      (h₂₂ := spMap (residue A)) ?_ (R.lift_snd _ _ w) R
    rw [R.lift_fst]
    exact H
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H2 hG

/- English proof (translation)
Establish `H` using `IsPullback.of_hasPullback p (spMap π)`. Establish `hqF : Flat (pullback.snd p (spMap π))` using `MorphismProperty.of_isPullback H hF`. Establish `hqP : IsProper (pullback.snd p (spMap π))` using `MorphismProperty.of_isPullback H hP`. Establish `hiso` using `isIso_appTop_of_artinian B _ (pullback.snd p (spMap π)) hqF hqP (geometricallyIntegral_fibre π hπ p hG)`. Take `⟨c, hc⟩` from `(ConcreteCategory.bijective_of_isIso (pullback.snd p (spMap π)).appTop).2 ((pullback.fst p (spMap π)).appTop f)`.

Set `e' : Sp B ⟶ pullback p (spMap π)` to `pullback.lift (spMap π ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])`. Establish `h1 : e'.appTop ((pullback.snd p (spMap π)).appTop c) = c`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd, Scheme.Hom.id_appTop]`. Both sides reduce to the same expression. Establish `h2 : e'.appTop ((pullback.fst p (spMap π)).appTop f) = 0`.

Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]`. Establish `hc0 : c = 0`. Rewrite `h1` using `[hc, h2]`. Conclude with `h1.symm`. Rewrite using `[← hc, hc0, map_zero]`.
-/
theorem appTop_fst_eq_zero {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [IsArtinianRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π]
    {X : Scheme.{0}} (p : X ⟶ Sp A) (e : Sp A ⟶ X) (he : e ≫ p = 𝟙 _) (hF : Flat p)
    (hP : IsProper p) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A))))
    (f : Γ(X, ⊤)) (hf : e.appTop f = 0) : (pullback.fst p (spMap π)).appTop f = 0 := by
  have H := IsPullback.of_hasPullback p (spMap π)
  have hqF : Flat (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hF
  have hqP : IsProper (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hP
  have hiso := isIso_appTop_of_artinian B _ (pullback.snd p (spMap π)) hqF hqP
    (geometricallyIntegral_fibre π hπ p hG)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (pullback.snd p (spMap π)).appTop).2
    ((pullback.fst p (spMap π)).appTop f)
  let e' : Sp B ⟶ pullback p (spMap π) :=
    pullback.lift (spMap π ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e'.appTop ((pullback.snd p (spMap π)).appTop c) = c := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd,
      Scheme.Hom.id_appTop]
    rfl
  have h2 : e'.appTop ((pullback.fst p (spMap π)).appTop f) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]
  have hc0 : c = 0 := by
    rw [hc, h2] at h1
    exact h1.symm
  rw [← hc, hc0, map_zero]

/- English proof (translation)
Introduce `r hr`. Take `⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv a = r` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Establish `h1` using `congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) a)`. Simplify using `only [CommRingCat.comp_apply] at h1`.

Establish `h2 : (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a) = 0` using `h1.trans hr`. Establish `h3 : Ideal.Quotient.mk I a = 0` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1 (h2.trans (map_zero _).symm)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h3`.
-/
theorem ker_appTop_le {A : Type} [CommRing A] (I : Ideal A) :
    RingHom.ker (spMap (Ideal.Quotient.mk I)).appTop.hom ≤
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  intro r hr
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv a = r :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r
  refine Ideal.mem_map_of_mem _ ?_
  have h1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) a)
  simp only [CommRingCat.comp_apply] at h1
  have h2 : (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a) = 0 :=
    h1.trans hr
  have h3 : Ideal.Quotient.mk I a = 0 :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1
      (h2.trans (map_zero _).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

/- English proof (translation)
Establish `hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A` using `Ideal.pow_le_self (Nat.succ_ne_zero n)`. Establish `hI : maximalIdeal A ^ (n + 1) ≠ ⊤` using `fun h ↦ Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))`. Establish `: Nontrivial (A ⧸ maximalIdeal A ^ (n + 1))` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Establish `hL : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1))` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Establish `hH : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))`.

Use `⟨fun a ha ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `ham : a ∈ maximalIdeal A` using `(mem_maximalIdeal a).mpr hna`. Establish `h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) = 0`. Rewrite using `[← map_pow]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)`. Use `(ha.pow (n + 1))` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `not_isUnit_zero this`. Establish `hK : Ring.KrullDimLE 0 (A ⧸ maximalIdeal A ^ (n + 1))`.

Use `Ring.krullDimLE_zero_iff.mpr fun Q hQ ↦ ?_` and prove the remaining obligations. Establish `: Q = maximalIdeal _`. Use `le_antisymm (le_maximalIdeal hQ.ne_top) fun b hb ↦ ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `ham : a ∈ maximalIdeal A`.

Rewrite `hb`, the goal using `[mem_maximalIdeal]`. Conclude with `fun hu ↦ hb (hu.map _)`. Establish `h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) ∈ Q`. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)]`. Conclude with `Q.zero_mem`.

Conclude with `hQ.mem_of_pow_mem _ h0`. Rewrite using `[this]`. Conclude with `maximalIdeal.isMaximal _`. Conclude with `⟨hL, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hH⟩`.
-/
theorem quotient_pow_facts (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    ∃ (_ : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)))
      (_ : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1))),
      IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  have hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hI : maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hL : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hH : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr hna
    have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)
    have := (ha.pow (n + 1))
    rw [h0] at this
    exact not_isUnit_zero this
  have hK : Ring.KrullDimLE 0 (A ⧸ maximalIdeal A ^ (n + 1)) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ ↦ ?_
    have : Q = maximalIdeal _ := by
      refine le_antisymm (le_maximalIdeal hQ.ne_top) fun b hb ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have ham : a ∈ maximalIdeal A := by
        rw [mem_maximalIdeal] at hb ⊢
        exact fun hu ↦ hb (hu.map _)
      have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) ∈ Q := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)]
        exact Q.zero_mem
      exact hQ.mem_of_pow_mem _ h0
    rw [this]
    exact maximalIdeal.isMaximal _
  exact ⟨hL, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hH⟩

/- English proof (translation)
Introduce `A _ _ _ X p e he hF hP hG`. Establish `h1 : p.appTop ≫ e.appTop = 𝟙 _`. Rewrite using `[← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]`. Establish `h2 : Function.Injective e.appTop`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `f hf`. Use `eq_zero_of_mem_pow p f fun n U ↦ ?_` and prove the remaining obligations. Take `⟨_, _, _⟩` from `quotient_pow_facts A n`. Establish `h0` using `appTop_fst_eq_zero (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) Ideal.Quotient.mk_surjective p e he hF hP hG f hf`. Establish `h3` using `mem_map_ker_of_app_eq_zero (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))) U.2 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f) (by`.

Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]`. Use `erw [h0]`. Conclude with `map_zero _)`. Conclude with `Ideal.map_mono (ker_appTop_le _) h3`. Establish `: Mono e.appTop` using `ConcreteCategory.mono_of_injective _ h2`.

Conclude with `⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩`.
-/
theorem isIso_appTop_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A) (e : Sp A ⟶ X), e ≫ p = 𝟙 _ → Flat p →
    IsProper p → GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) →
    IsIso p.appTop := by
  intro A _ _ _ X p e he hF hP hG
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    refine eq_zero_of_mem_pow p f fun n U ↦ ?_
    obtain ⟨_, _, _⟩ := quotient_pow_facts A n
    have h0 := appTop_fst_eq_zero (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
      Ideal.Quotient.mk_surjective p e he hF hP hG f hf
    have h3 := mem_map_ker_of_app_eq_zero
      (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))) U.2
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f) (by
        rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        erw [h0]
        exact map_zero _)
    exact Ideal.map_mono (ker_appTop_le _) h3
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
