import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(φ.hom.app (op U) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x`. Rewrite using `[φ.hom.naturality]`.
-/
private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H)
    {U : Scheme.{0}} (x : Sec F U) : Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

/- English proof (translation)
Rewrite using `[sec_map_res, CupSpec.freeGen_res]`. Establish `e : (ConcreteCategory.hom ((yoneda.obj W).map i.op)) (𝟙 W) = (ConcreteCategory.hom ((yoneda.map i).app (op A))) (𝟙 A)` using `by simp`. Rewrite using `[e, ← CupSpec.freeGen_map, ← sec_map_comp, h0, sec_map_zero]`.
-/
private lemma res_univ_eq_zero {R : Type} [CommRing R] {A W : Scheme.{0}} (i : A ⟶ W) {Z : Shv R}
    (h : (free R).obj (yoneda.obj W) ⟶ Z) (h0 : (free R).map (yoneda.map i) ≫ h = 0) :
    Sec.res i (Sec.map h (freeGen R (yoneda.obj W) W (𝟙 W))) = 0 := by
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj W).map i.op)) (𝟙 W) =
      (ConcreteCategory.hom ((yoneda.map i).app (op A))) (𝟙 A) := by simp
  rw [e, ← CupSpec.freeGen_map, ← sec_map_comp, h0, sec_map_zero]

/- English proof (translation)
Introduce `R _ X U V`. Apply `Preadditive.epi_of_cancel_zero` to reduce the goal to its premises. Introduce `Z g hg`. Set `ι` to `{O : X.Opens // O = U ∨ O = V}`. Establish `hle : ∀ i : ι, i.1 ≤ U ⊔ V`.

Introduce and unpack `⟨O, rfl | rfl⟩`. Conclude with `le_sup_left`. Conclude with `le_sup_right`. Establish `gz : ∀ i : ι, (free R).map (yoneda.map (X.homOfLE (hle i))) ≫ g = 0`. Introduce and unpack `⟨O, rfl | rfl⟩`.

Use `congrArg (biprod.inl ≫ ·) hg` as an intermediate fact. Simplify using `using this`. Use `congrArg (biprod.inr ≫ ·) hg` as an intermediate fact. Simplify using `using this`. Establish `cover : ∀ (O : X.Opens) (hO : O ≤ U ⊔ V) (y : (U ⊔ V : X.Opens).toScheme), (U ⊔ V).ι y ∈ O → ∃ z, X.homOfLE hO z = y`.

Introduce `O hO y hy`. Establish `hy' : (U ⊔ V).ι y ∈ Set.range O.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hy`. Take `⟨z, hz⟩` from `hy'`.

Use `⟨z, (U ⊔ V).ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(X.homOfLE hO ≫ (U ⊔ V).ι) z = _`. Rewrite using `[Scheme.homOfLE_ι, hz]`. Use `CupSpec.free_ext g 0 (fun T x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.map g (freeGen R _ T x) = 0`.

Set `xx : T ⟶ (U ⊔ V : X.Opens).toScheme` to `x`. Take `⟨hsep, -⟩` from `sec_sep_glue_of_points R Z T ι (fun i => pullback x (X.homOfLE (hle i))) (fun i => pullback.fst x (X.homOfLE (hle i))) (fun i => inferInstance) (by`. Introduce `t`. Establish `hy : (U ⊔ V).ι (xx t) ∈ ((U ⊔ V : X.Opens) : Set X)`. Rewrite using `[← Scheme.Opens.range_ι]`.

Conclude with `⟨xx t, rfl⟩`. Rewrite `hy` using `[TopologicalSpace.Opens.coe_sup]`. Break down `hy with hU | hV` into its components or cases. Take `⟨z, hz⟩` from `cover U le_sup_left (xx t) hU`. Establish `ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨U, Or.inl rfl⟩)))`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨z, hz⟩`. Take `⟨v, hv⟩` from `ht`. Conclude with `⟨⟨U, Or.inl rfl⟩, v, hv⟩`. Take `⟨z, hz⟩` from `cover V le_sup_right (xx t) hV`.

Establish `ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨V, Or.inr rfl⟩)))`. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨z, hz⟩`. Take `⟨v, hv⟩` from `ht`. Conclude with `⟨⟨V, Or.inr rfl⟩, v, hv⟩)`.

Apply `hsep` to reduce the goal to its premises. Introduce `i`. Establish `z : Sec.map g (freeGen R (yoneda.obj (U ⊔ V : X.Opens).toScheme) i.1.toScheme (X.homOfLE (hle i))) = 0`. Use `res_univ_eq_zero (X.homOfLE (hle i)) g (gz i)` as an intermediate fact. Rewrite `this` using `[sec_map_res, CupSpec.freeGen_res, show (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map (X.homOfLE (hle i)).op)) (𝟙 _) = X.homOfLE (hle i) by simp]`. Then use the resulting hypothesis.

Rewrite using `[sec_map_res, CupSpec.freeGen_res]`. Establish `e : (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map (pullback.fst x (X.homOfLE (hle i))).op)) x = (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map (pullback.snd x (X.homOfLE (hle i))).op)) (X.homOfLE (hle i))`. Simplify using `[pullback.condition]`. Rewrite using `[e, ← CupSpec.freeGen_res, ← sec_map_res, z]`. Conclude with `map_zero _`.
-/
theorem UpperTheory.etale_purity_free_cover :
    LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := by
  intro R _ X U V
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  let ι := {O : X.Opens // O = U ∨ O = V}
  have hle : ∀ i : ι, i.1 ≤ U ⊔ V := by
    rintro ⟨O, rfl | rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  have gz : ∀ i : ι, (free R).map (yoneda.map (X.homOfLE (hle i))) ≫ g = 0 := by
    rintro ⟨O, rfl | rfl⟩
    · have := congrArg (biprod.inl ≫ ·) hg
      simpa using this
    · have := congrArg (biprod.inr ≫ ·) hg
      simpa using this
  have cover : ∀ (O : X.Opens) (hO : O ≤ U ⊔ V) (y : (U ⊔ V : X.Opens).toScheme),
      (U ⊔ V).ι y ∈ O → ∃ z, X.homOfLE hO z = y := by
    intro O hO y hy
    have hy' : (U ⊔ V).ι y ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    refine ⟨z, (U ⊔ V).ι.isOpenEmbedding.injective ?_⟩
    change (X.homOfLE hO ≫ (U ⊔ V).ι) z = _
    rw [Scheme.homOfLE_ι, hz]
  refine CupSpec.free_ext g 0 (fun T x => ?_)
  change Sec.map g (freeGen R _ T x) = 0
  let xx : T ⟶ (U ⊔ V : X.Opens).toScheme := x
  obtain ⟨hsep, -⟩ := sec_sep_glue_of_points R Z T ι (fun i => pullback x (X.homOfLE (hle i)))
    (fun i => pullback.fst x (X.homOfLE (hle i))) (fun i => inferInstance) (by
      intro t
      have hy : (U ⊔ V).ι (xx t) ∈ ((U ⊔ V : X.Opens) : Set X) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨xx t, rfl⟩
      rw [TopologicalSpace.Opens.coe_sup] at hy
      rcases hy with hU | hV
      · obtain ⟨z, hz⟩ := cover U le_sup_left (xx t) hU
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨U, Or.inl rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨U, Or.inl rfl⟩, v, hv⟩
      · obtain ⟨z, hz⟩ := cover V le_sup_right (xx t) hV
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨V, Or.inr rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨V, Or.inr rfl⟩, v, hv⟩)
  apply hsep
  intro i
  have z : Sec.map g (freeGen R (yoneda.obj (U ⊔ V : X.Opens).toScheme) i.1.toScheme (X.homOfLE (hle i))) = 0 := by
    have := res_univ_eq_zero (X.homOfLE (hle i)) g (gz i)
    rwa [sec_map_res, CupSpec.freeGen_res, show (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (X.homOfLE (hle i)).op)) (𝟙 _) = X.homOfLE (hle i) by simp] at this
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.fst x (X.homOfLE (hle i))).op)) x =
      (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.snd x (X.homOfLE (hle i))).op)) (X.homOfLE (hle i)) := by
    simp [pullback.condition]
  rw [e, ← CupSpec.freeGen_res, ← sec_map_res, z]
  exact map_zero _
