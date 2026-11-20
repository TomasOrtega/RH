import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R' ⟶ UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

/- English proof (translation)
Apply the tactic sequence `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in`. Introduce `A _ Y Z f g s _ h N I hI hn`. Set `X' : Over Z` to `Over.mk (f ≫ s)`. Set `Y' : Over Z` to `Over.mk s`. Set `f' : X' ⟶ Y'` to `Over.homMk f`.

Set `g' : X' ⟶ Y'` to `Over.homMk g h.symm`. Establish `: IsSeparated Y'.hom` using `‹_›`. Establish `: IsAffine X'.left` using `inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))`. Establish `hcl : IsClosedImmersion (equalizer.ι f' g').left` using `inferInstance`. Take `⟨haff, hsurj⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left`.

Establish `hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left, l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))`. Introduce `n`. Set `T' : Over Z` to `Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)`. Set `ι' : T' ⟶ X'` to `Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))`. Establish `hc : ι' ≫ f' = ι' ≫ g'` using `by ext1`.

Conclude with `hn n`. Use `⟨(equalizer.lift ι' hc).left, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.comp_left, equalizer.lift_ι]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective (equalizer.ι f' g').left.appTop`.

Use `(injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_` and prove the remaining obligations. Take `⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y` from `⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩`. Establish `ha : a = 0`. Use `hI a fun n ↦ ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `hfac n`.

Establish `h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0`. Rewrite using `[← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Use `erw [hy]`. Conclude with `map_zero _`. Establish `h2` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))`.

Establish `h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0`. Establish `h4` using `congr($h2 a)`. Simplify using `only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4`. Conclude with `h4.trans h1`. Establish `h5` using `congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)`.

Simplify using `only [map_zero] at h5`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using h5`. Simplify using `[ha]`. Establish `hiso : IsIso (equalizer.ι f' g').left.appTop`.

Conclude with `(ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩`. Establish `hE : IsIso (equalizer.ι f' g').left` using `(MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))`. Rewrite using `[← cancel_epi (equalizer.ι f' g').left]`. Conclude with `congr($(equalizer.condition f' g').left)`.
-/
theorem UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main :
    ∀ {A : Type} [inst : CommRing A] {Y Z : AlgebraicGeometry.Scheme} {f g : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp A ⟶ Y} (s : Y ⟶ Z)
      [AlgebraicGeometry.IsSeparated s],
      CategoryTheory.CategoryStruct.comp f s = CategoryTheory.CategoryStruct.comp g s →
        ∀ {N : Type} (I : N → Ideal A),
          (∀ (x : A), (∀ (n : N), x ∈ I n) → x = (0 : A)) →
            (∀ (n : N),
                CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) f =
                  CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) g) →
              f = g := by
  open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
  intro A _ Y Z f g s _ h N I hI hn
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : IsSeparated Y'.hom := ‹_›
  have : IsAffine X'.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hcl : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left,
      l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) := by
    intro n
    let T' : Over Z := Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)
    let ι' : T' ⟶ X' := Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))
    have hc : ι' ≫ f' = ι' ≫ g' := by
      ext1
      exact hn n
    refine ⟨(equalizer.lift ι' hc).left, ?_⟩
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop := by
    refine (injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩
    have ha : a = 0 := by
      refine hI a fun n ↦ ?_
      obtain ⟨l, hl⟩ := hfac n
      have h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0 := by
        rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [hy]
        exact map_zero _
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0 := by
        have h4 := congr($h2 a)
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4
        exact h4.trans h1
      have h5 := congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)
      simp only [map_zero] at h5
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using h5
    simp [ha]
  have hiso : IsIso (equalizer.ι f' g').left.appTop := by
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  have hE : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
