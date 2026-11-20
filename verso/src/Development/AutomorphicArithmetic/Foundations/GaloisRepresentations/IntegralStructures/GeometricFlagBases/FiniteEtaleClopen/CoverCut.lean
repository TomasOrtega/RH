import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

open GlobalTheory.GalV (Splits)

/- English proof (translation)
Take `⟨h, hi⟩` from `h`. Establish `h' : ∀ j, a j ≫ f = f` using `fun j => (cancel_mono m).1 (by rw [Category.assoc]; exact h j)`. Use `⟨h', ?_⟩` and prove the remaining obligations. Set `e : pullback f f ⟶ pullback (f ≫ m) (f ≫ m)` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])`. Set `e' : pullback (f ≫ m) (f ≫ m) ⟶ pullback f f` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [← cancel_mono m, Category.assoc, Category.assoc, pullback.condition])`.

Use `haveI : IsIso e := ⟨⟨e', by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [e, e', Category.assoc, Category.id_comp] repeat' rw [pullback.lift_fst]`. Simplify using `only [e, e', Category.assoc, Category.id_comp] repeat' rw [pullback.lift_snd], by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [e, e', Category.assoc, Category.id_comp] repeat' rw [pullback.lift_fst]`. Simplify using `only [e, e', Category.assoc, Category.id_comp] repeat' rw [pullback.lift_snd]⟩⟩`. Establish `heq : (Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) : (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e = Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h j])`. Apply `Limits.Sigma.hom_ext` to reduce the goal to its premises. Introduce `j`.

Simplify using `only [Limits.colimit.ι_desc_assoc, Limits.colimit.ι_desc, Limits.Cofan.mk_ι_app]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [e, Category.assoc] repeat' rw [pullback.lift_fst]`. Simplify using `only [e, Category.assoc] repeat' rw [pullback.lift_snd]`. Use `haveI : IsIso ((Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) : (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e) := by`.

Rewrite using `[heq]`. Conclude with `hi`. Conclude with `IsIso.of_isIso_comp_right _ e`.
-/
private theorem splits_cancel {A B Z : Scheme.{0}} (m : A ⟶ B) [Mono m] (f : Z ⟶ A) {J : Type}
    (a : J → (Z ⟶ Z)) (h : Splits (f ≫ m) (f ≫ m) a) : Splits f f a := by
  obtain ⟨h, hi⟩ := h
  have h' : ∀ j, a j ≫ f = f := fun j =>
    (cancel_mono m).1 (by rw [Category.assoc]; exact h j)
  refine ⟨h', ?_⟩
  let e : pullback f f ⟶ pullback (f ≫ m) (f ≫ m) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  let e' : pullback (f ≫ m) (f ≫ m) ⟶ pullback f f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      (by rw [← cancel_mono m, Category.assoc, Category.assoc, pullback.condition])
  haveI : IsIso e := ⟨⟨e', by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd], by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd]⟩⟩
  have heq : (Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e =
      Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h j]) := by
    apply Limits.Sigma.hom_ext
    intro j
    simp only [Limits.colimit.ι_desc_assoc, Limits.colimit.ι_desc, Limits.Cofan.mk_ι_app]
    apply pullback.hom_ext
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_fst]
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_snd]
  haveI : IsIso ((Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e) := by
    rw [heq]
    exact hi
  exact IsIso.of_isIso_comp_right _ e

end UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Introduce `k L O _ _ _ _ H θ C V hVcl hpre`. Establish `hV : ∀ z, C.π z ∈ V`. Introduce `z`. Establish `hz : pullback.lift C.π H.q C.ov z ∈ ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y)`. Rewrite using `[hpre]`.

Conclude with `⟨z, rfl⟩`. Simplify `hz` using `only [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, SetLike.mem_coe]`. Establish `hrange : Set.range ⇑C.π ⊆ Set.range ⇑V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨z, rfl⟩`.

Conclude with `hV z`. Set `π' : H.Z ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι C.π hrange`. Establish `hπ' : π' ≫ V.ι = C.π` using `IsOpenImmersion.lift_fac V.ι C.π hrange`. Establish `ov' : π' ≫ (V.ι ≫ C.p) = H.q ≫ gen O k`. Rewrite using `[← Category.assoc, hπ']`.

Conclude with `C.ov`. Set `m : pullback (V.ι ≫ C.p) (gen O k) ⟶ pullback C.p (gen O k)` to `pullback.lift (pullback.fst _ _ ≫ V.ι) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)`. Establish `hsq : IsPullback (pullback.fst (V.ι ≫ C.p) (gen O k)) m V.ι (pullback.fst C.p (gen O k))`. Use `IsPullback.of_bot (v₂₁ := pullback.snd C.p (gen O k)) (v₂₂ := C.p) (h₃₁ := gen O k) ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k))` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`.

Conclude with `IsPullback.of_hasPullback (V.ι ≫ C.p) (gen O k)`. Rewrite using `[pullback.lift_fst]`. Use `haveI hmo : IsOpenImmersion m := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion V.ι))`. Set `L' : H.Z ⟶ pullback (V.ι ≫ C.p) (gen O k)` to `pullback.lift π' H.q ov'`. Establish `hLm : L' ≫ m = pullback.lift C.π H.q C.ov`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [L', m, Category.assoc]`. Rewrite using `[pullback.lift_fst, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hπ']`. Simplify using `only [L', m, Category.assoc]`. Rewrite using `[pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]`.

Use `haveI : Smooth C.p := C.smooth`. Use `haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVcl)`. Use `haveI hfin : IsFinite (L' ≫ m) := by`. Rewrite using `[hLm]`. Conclude with `C.finπ`.

Use `haveI het : Etale (L' ≫ m) := by`. Rewrite using `[hLm]`. Conclude with `C.etπ`. Establish `spl' : GlobalTheory.GalV.Splits L' L' C.a`. Apply `splits_cancel m L' C.a` to reduce the goal to its premises.

Rewrite using `[hLm]`. Conclude with `C.spl`. Establish `hproj : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (V.ι ≫ C.p)`. Take `⟨N, i, hi, hic⟩` from `C.proj`. Use `haveI := hi`.

Conclude with `⟨N, V.ι ≫ i, inferInstance, by rw [Category.assoc, hic]⟩`. Establish `hdim : ∃ d, SmoothOfRelativeDimension d (V.ι ≫ C.p)`. Take `⟨d, hd⟩` from `C.dim`. Conclude with `⟨d, HasRingHomProperty.comp_of_isOpenImmersion (P := @SmoothOfRelativeDimension d) _ _ hd⟩`. Establish `honto : AlgebraicGeometry.Surjective L'`.

Use `⟨fun w => ?_⟩` and prove the remaining obligations. Establish `hw : m w ∈ ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y)`. Rewrite using `[Set.mem_preimage, ← Scheme.Hom.comp_apply]`. Simplify using `only [m]`. Rewrite using `[pullback.lift_fst, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι V]`.

Conclude with `⟨_, rfl⟩`. Rewrite `hw` using `[hpre]`. Take `⟨z, hz⟩` from `hw`. Use `⟨z, m.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hLm, hz]`.

Conclude with `⟨Cover.mk V.toScheme (V.ι ≫ C.p) inferInstance hproj π' ov' C.Δ (grp := C.grp) (fin := C.fin) C.a (IsFinite.of_comp L' m) (Etale.of_comp L' m) C.one C.mul spl' C.fix hdim, V.ι, ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hVcl⟩, Scheme.Opens.range_ι V, rfl, hπ', honto⟩`.
-/
theorem UpperTheory.Gal.Int.Geo.Cut.coverCut :
    UpperTheory.Gal.Int.Geo.Cut.CoverCut := by
  intro k L O _ _ _ _ H θ C V hVcl hpre
  have hV : ∀ z, C.π z ∈ V := by
    intro z
    have hz : pullback.lift C.π H.q C.ov z ∈
        ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [hpre]
      exact ⟨z, rfl⟩
    simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst,
      SetLike.mem_coe] using hz
  have hrange : Set.range ⇑C.π ⊆ Set.range ⇑V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hV z
  let π' : H.Z ⟶ V.toScheme := IsOpenImmersion.lift V.ι C.π hrange
  have hπ' : π' ≫ V.ι = C.π := IsOpenImmersion.lift_fac V.ι C.π hrange
  have ov' : π' ≫ (V.ι ≫ C.p) = H.q ≫ gen O k := by
    rw [← Category.assoc, hπ']
    exact C.ov
  let m : pullback (V.ι ≫ C.p) (gen O k) ⟶ pullback C.p (gen O k) :=
    pullback.lift (pullback.fst _ _ ≫ V.ι) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hsq : IsPullback (pullback.fst (V.ι ≫ C.p) (gen O k)) m V.ι
      (pullback.fst C.p (gen O k)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd C.p (gen O k)) (v₂₂ := C.p)
      (h₃₁ := gen O k) ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k))
    · rw [pullback.lift_snd]
      exact IsPullback.of_hasPullback (V.ι ≫ C.p) (gen O k)
    · rw [pullback.lift_fst]
  haveI hmo : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq
      (inferInstanceAs (IsOpenImmersion V.ι))
  let L' : H.Z ⟶ pullback (V.ι ≫ C.p) (gen O k) := pullback.lift π' H.q ov'
  have hLm : L' ≫ m = pullback.lift C.π H.q C.ov := by
    apply pullback.hom_ext
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hπ']
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  haveI : Smooth C.p := C.smooth
  haveI : IsClosedImmersion V.ι :=
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVcl)
  haveI hfin : IsFinite (L' ≫ m) := by
    rw [hLm]
    exact C.finπ
  haveI het : Etale (L' ≫ m) := by
    rw [hLm]
    exact C.etπ
  have spl' : GlobalTheory.GalV.Splits L' L' C.a := by
    apply splits_cancel m L' C.a
    rw [hLm]
    exact C.spl
  have hproj : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (V.ι ≫ C.p) := by
    obtain ⟨N, i, hi, hic⟩ := C.proj
    haveI := hi
    exact ⟨N, V.ι ≫ i, inferInstance, by rw [Category.assoc, hic]⟩
  have hdim : ∃ d, SmoothOfRelativeDimension d (V.ι ≫ C.p) := by
    obtain ⟨d, hd⟩ := C.dim
    exact ⟨d, HasRingHomProperty.comp_of_isOpenImmersion
      (P := @SmoothOfRelativeDimension d) _ _ hd⟩
  have honto : AlgebraicGeometry.Surjective L' := by
    refine ⟨fun w => ?_⟩
    have hw : m w ∈ ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      simp only [m]
      rw [pullback.lift_fst, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι V]
      exact ⟨_, rfl⟩
    rw [hpre] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨z, m.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hLm, hz]
  exact ⟨Cover.mk V.toScheme (V.ι ≫ C.p) inferInstance hproj π' ov' C.Δ (grp := C.grp)
      (fin := C.fin) C.a (IsFinite.of_comp L' m) (Etale.of_comp L' m) C.one C.mul spl'
      C.fix hdim,
    V.ι, ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hVcl⟩,
    Scheme.Opens.range_ι V, rfl, hπ', honto⟩
