import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsMonHomSplitTorusOfSqEqBot

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusLift

section General

variable {S S' S'' : Scheme.{0}}

/- English proof (translation)
Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem map_left_fst (p : S' ⟶ S) {V W : Over S} (f : V ⟶ W) :
    ((Over.pullback p).map f).left ≫ pullback.fst W.hom p = pullback.fst V.hom p ≫ f.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext h` to reduce the goal to its premises. Establish `ha` using `Over.w a`. Establish `hb` using `Over.w b`. Simplify using `only [Over.pullback_obj_hom] at ha hb`.

Simplify using `[ha, hb]`.
-/
theorem hom_ext_fst (p : S' ⟶ S) {Z : Over S'} {W : Over S} {a b : Z ⟶ (Over.pullback p).obj W}
    (h : a.left ≫ pullback.fst W.hom p = b.left ≫ pullback.fst W.hom p) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  have ha := Over.w a
  have hb := Over.w b
  simp only [Over.pullback_obj_hom] at ha hb
  simp [ha, hb]

/- English proof (translation)
Substitute `h` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `hfg`. Establish `h1` using `(Over.pullbackComp s p).hom.naturality f`. Establish `h2` using `(Over.pullbackComp s p).hom.naturality g`.

Simplify using `only [Functor.comp_map] at h1 h2`. Apply `(cancel_epi ((Over.pullbackComp s p).hom.app V)).1` to reduce the goal to its premises. Rewrite using `[← h1, ← h2, hfg]`. Introduce `hfg`. Establish `h1` using `(Over.pullbackComp s p).inv.naturality f`.

Establish `h2` using `(Over.pullbackComp s p).inv.naturality g`. Simplify using `only [Functor.comp_map] at h1 h2`. Apply `(cancel_epi ((Over.pullbackComp s p).inv.app V)).1` to reduce the goal to its premises. Rewrite using `[← h1, ← h2, hfg]`.
-/
theorem map_eq_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p) {V W : Over S}
    (f g : V ⟶ W) : (Over.pullback q).map f = (Over.pullback q).map g ↔
      (Over.pullback s).map ((Over.pullback p).map f) =
        (Over.pullback s).map ((Over.pullback p).map g) := by
  subst h
  constructor
  · intro hfg
    have h1 := (Over.pullbackComp s p).hom.naturality f
    have h2 := (Over.pullbackComp s p).hom.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).hom.app V)).1
    rw [← h1, ← h2, hfg]
  · intro hfg
    have h1 := (Over.pullbackComp s p).inv.naturality f
    have h2 := (Over.pullbackComp s p).inv.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).inv.app V)).1
    rw [← h1, ← h2, hfg]

/- English proof (translation)
Apply `hom_ext_fst` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `using h`. Establish `ha` using `Over.w a`. Establish `hb` using `Over.w b`.

Simplify using `only [Over.pullback_obj_hom] at ha hb`. Simplify using `only [Category.assoc, Over.pullback_obj_left, Over.pullback_obj_hom] at *`. Rewrite using `[pullback.condition, reassoc_of% ha, reassoc_of% hb]`.
-/
private theorem pullback_pullback_hom_ext {s : S'' ⟶ S'} {p : S' ⟶ S} {G : Over S} {Z : Over S''}
    {a b : Z ⟶ (Over.pullback s).obj ((Over.pullback p).obj G)}
    (h : a.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p = b.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p) :
    a = b := by
  apply hom_ext_fst
  apply pullback.hom_ext
  · simpa using h
  · have ha := Over.w a
    have hb := Over.w b
    simp only [Over.pullback_obj_hom] at ha hb
    simp only [Category.assoc, Over.pullback_obj_left, Over.pullback_obj_hom] at *
    rw [pullback.condition, reassoc_of% ha, reassoc_of% hb]

/- English proof (translation)
Establish `h` using `congrArg (fun x => x.left) (conjugateEquiv_counit (Over.mapPullbackAdj (s ≫ p)) ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj p)) (Over.mapComp s p).symm.hom G)`. Simplify `h` using `[Over.pullbackComp]`.
-/
private theorem pullbackComp_hom_fst_fst (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) :
    ((Over.pullbackComp s p).hom.app G).left ≫ pullback.fst _ s ≫ pullback.fst G.hom p =
      pullback.fst G.hom (s ≫ p) := by
  have h := congrArg (fun x => x.left) (conjugateEquiv_counit (Over.mapPullbackAdj (s ≫ p))
    ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj p)) (Over.mapComp s p).symm.hom G)
  simpa [Over.pullbackComp] using h

/- English proof (translation)
Take `⟨e, he, hc⟩` from `GlobalTheory.exists_pullback_comp_iso_monHom s p (s ≫ p) rfl G`. Establish `: (Over.pullbackComp s p).hom.app G = e.hom`. Apply `pullback_pullback_hom_ext` to reduce the goal to its premises. Rewrite using `[hc, pullbackComp_hom_fst_fst]`. Rewrite using `[this]`.

Conclude with `he`.
-/
theorem isMonHom_pullbackComp (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.exists_pullback_comp_iso_monHom s p (s ≫ p) rfl G
  have : (Over.pullbackComp s p).hom.app G = e.hom := by
    apply pullback_pullback_hom_ext
    rw [hc, pullbackComp_hom_fst_fst]
  rw [this]
  exact he

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : g' = (asIso a).inv ≫ g ≫ b` using `by simp [hg]`. Rewrite using `[e]`. Use `infer_instance`.

Introduce `h`. Establish `e : g = a ≫ g' ≫ (asIso b).inv` using `by simp [← reassoc_of% hg]`. Rewrite using `[e]`. Use `infer_instance`.
-/
private theorem isMonHom_iff_of_conj_iso {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    [MonObj M] [MonObj M'] [MonObj N] [MonObj N'] (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b]
    (ha : IsMonHom a) (hb : IsMonHom b) (g : M ⟶ N) (g' : M' ⟶ N') (hg : g ≫ b = a ≫ g') :
    IsMonHom g ↔ IsMonHom g' := by
  constructor
  · intro h
    have e : g' = (asIso a).inv ≫ g ≫ b := by simp [hg]
    rw [e]
    infer_instance
  · intro h
    have e : g = a ≫ g' ≫ (asIso b).inv := by simp [← reassoc_of% hg]
    rw [e]
    infer_instance

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `isMonHom_iff_of_conj_iso _ _ (isMonHom_pullbackComp s p V) (isMonHom_pullbackComp s p W) _ _ ((Over.pullbackComp s p).hom.naturality f)`.
-/
theorem isMonHom_map_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p)
    {V W : Over S} [GrpObj V] [GrpObj W] (f : V ⟶ W) : IsMonHom ((Over.pullback q).map f) ↔
      IsMonHom ((Over.pullback s).map ((Over.pullback p).map f)) := by
  subst h
  exact isMonHom_iff_of_conj_iso _ _ (isMonHom_pullbackComp s p V) (isMonHom_pullbackComp s p W) _ _
    ((Over.pullbackComp s p).hom.naturality f)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨x, rfl⟩` from `i.surjective y`. Establish `hx : x ∈ (i ≫ f) ⁻¹ᵁ U` using `by rw [h]; trivial`. Simplify using `using hx`.
-/
theorem preimage_eq_top_of_surjective {X Y Z : Scheme.{0}} (i : X ⟶ Y) [Surjective i] (f : Y ⟶ Z)
    {U : Z.Opens} (h : (i ≫ f) ⁻¹ᵁ U = ⊤) : f ⁻¹ᵁ U = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := i.surjective y
  have hx : x ∈ (i ≫ f) ⁻¹ᵁ U := by rw [h]; trivial
  simpa using hx

end General

/- English proof (translation)
Take `⟨n, hn⟩` from `h`. Establish `hh : IsHomeomorph (PrimeSpectrum.comap β.hom)`. Use `PrimeSpectrum.isHomeomorph_comap β.hom (fun x => ⟨1, one_pos, ?_⟩) ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hβ x`. Conclude with `⟨y, by simp⟩`.

Introduce `x hx`. Establish `hxn : x ^ n ∈ RingHom.ker β.hom ^ n` using `Ideal.pow_mem_pow hx n`. Rewrite `hxn` using `[hn, Ideal.zero_eq_bot, Ideal.mem_bot]`. Conclude with `mem_nilradical.2 ⟨n, hxn⟩`. Conclude with `⟨hh.surjective⟩`.
-/
theorem surjective_specMap {A C : CommRingCat.{0}} (β : A ⟶ C) (hβ : Function.Surjective β)
    (h : IsNilpotent (RingHom.ker β.hom)) : Surjective (Spec.map β) := by
  obtain ⟨n, hn⟩ := h
  have hh : IsHomeomorph (PrimeSpectrum.comap β.hom) := by
    refine PrimeSpectrum.isHomeomorph_comap β.hom (fun x => ⟨1, one_pos, ?_⟩) ?_
    · obtain ⟨y, rfl⟩ := hβ x
      exact ⟨y, by simp⟩
    · intro x hx
      have hxn : x ^ n ∈ RingHom.ker β.hom ^ n := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hxn
      exact mem_nilradical.2 ⟨n, hxn⟩
  exact ⟨hh.surjective⟩

/- English proof (translation)
Use `GlobalTheory.TorusNil.isIso_torusPt_of A X` as an intermediate fact. Establish `: IsAffine (GlobalTheory.TorusNil.sp A (AddMonoidAlgebra A X)).left` using `by dsimp [GlobalTheory.TorusNil.sp] infer_instance`. Conclude with `IsAffine.of_isIso (inv (GlobalTheory.TorusNil.torusPt A X (AddMonoidAlgebra.of A X)).left)`.
-/
theorem isAffine_splitTorus (A : Type) [CommRing A] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left := by
  have := GlobalTheory.TorusNil.isIso_torusPt_of A X
  have : IsAffine (GlobalTheory.TorusNil.sp A (AddMonoidAlgebra A X)).left := by
    dsimp [GlobalTheory.TorusNil.sp]
    infer_instance
  exact IsAffine.of_isIso (inv (GlobalTheory.TorusNil.torusPt A X (AddMonoidAlgebra.of A X)).left)

/- English proof (translation)
Use `isAffine_splitTorus A X` as an intermediate fact. Establish `hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` using `surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)`. Take `⟨f, hf⟩` from `GlobalTheory.NilpotentLift.main A J hJ G (splitTorus (Spec (CommRingCat.of A)) X) (g.left ≫ pullback.fst _ _) (by`. Establish `hw` using `Over.w g`. Simplify using `only [Over.pullback_obj_hom] at hw`.

Rewrite using `[Category.assoc, pullback.condition (f := G.hom), reassoc_of% hw]`. Conclude with `pullback.condition.symm) ⟨W, hW, hg⟩`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Apply `preimage_eq_top_of_surjective (pullback.fst (splitTorus (Spec (CommRingCat.of A)) X).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))` to reduce the goal to its premises. Rewrite using `[hf]`.

Conclude with `hg`. Apply `hom_ext_fst` to reduce the goal to its premises. Rewrite using `[map_left_fst, hf]`.
-/
theorem exists_lift {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [Smooth G.hom]
    (g : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G)
    {W : G.left.Opens} (hW : IsAffineOpen W) (hg : (g.left ≫ pullback.fst _ _) ⁻¹ᵁ W = ⊤) :
    ∃ f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, f.left ⁻¹ᵁ W = ⊤ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f = g := by
  have := isAffine_splitTorus A X
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  obtain ⟨f, hf⟩ := GlobalTheory.NilpotentLift.main A J hJ G (splitTorus (Spec (CommRingCat.of A)) X)
    (g.left ≫ pullback.fst _ _) (by
      have hw := Over.w g
      simp only [Over.pullback_obj_hom] at hw
      rw [Category.assoc, pullback.condition (f := G.hom), reassoc_of% hw]
      exact pullback.condition.symm) ⟨W, hW, hg⟩
  refine ⟨f, ?_, ?_⟩
  · apply preimage_eq_top_of_surjective
      (pullback.fst (splitTorus (Spec (CommRingCat.of A)) X).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    rw [hf]
    exact hg
  · apply hom_ext_fst
    rw [map_left_fst, hf]

/- English proof (translation)
Substitute `hker` using the available equality. Set `e` to `RingHom.quotientKerEquivOfSurjective (f := β.hom) hβ`. Use `⟨CommRingCat.ofHom e.symm.toRingHom, CommRingCat.ofHom e.toRingHom, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `e.symm (β.hom a) = Ideal.Quotient.mk _ a`.

Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use extensionality with `a`. Both sides reduce to the same expression.
-/
private theorem exists_factor_through_quotient_of_surjective {A : Type} [CommRing A] (J : Ideal A) {C : CommRingCat.{0}}
    (β : CommRingCat.of A ⟶ C) (hβ : Function.Surjective β) (hker : RingHom.ker β.hom = J) :
    ∃ (g0 : C ⟶ CommRingCat.of (A ⧸ J)) (d0 : CommRingCat.of (A ⧸ J) ⟶ C),
      β ≫ g0 = CommRingCat.ofHom (Ideal.Quotient.mk J) ∧
        CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ d0 = β := by
  subst hker
  let e := RingHom.quotientKerEquivOfSurjective (f := β.hom) hβ
  refine ⟨CommRingCat.ofHom e.symm.toRingHom, CommRingCat.ofHom e.toRingHom, ?_, ?_⟩
  · ext a
    change e.symm (β.hom a) = Ideal.Quotient.mk _ a
    rw [RingEquiv.symm_apply_eq]
    rfl
  · ext a
    rfl

/- English proof (translation)
Use `⟨⟨fun h => (map_eq_iff hq f g).2 (by rw [h]), fun h => (map_eq_iff hp f g).2 (by rw [h])⟩, ⟨fun h => (isMonHom_map_iff hq f).2 (by infer_instance), fun h => (isMonHom_map_iff hp f).2 (by infer_instance)⟩⟩` and prove the remaining obligations.
-/
private theorem pullback_map_eq_iff_and_isMonHom_iff {S S' S'' : Scheme.{0}} {p : S' ⟶ S} {q : S'' ⟶ S} (s : S'' ⟶ S')
    (t : S' ⟶ S'') (hq : q = s ≫ p) (hp : p = t ≫ q) {V W : Over S} [GrpObj V] [GrpObj W]
    (f g : V ⟶ W) :
    ((Over.pullback p).map f = (Over.pullback p).map g ↔
        (Over.pullback q).map f = (Over.pullback q).map g) ∧
      (IsMonHom ((Over.pullback p).map f) ↔ IsMonHom ((Over.pullback q).map f)) := by
  refine ⟨⟨fun h => (map_eq_iff hq f g).2 (by rw [h]), fun h => (map_eq_iff hp f g).2 (by rw [h])⟩,
    ⟨fun h => (isMonHom_map_iff hq f).2 (by infer_instance),
      fun h => (isMonHom_map_iff hp f).2 (by infer_instance)⟩⟩

/- English proof (translation)
Apply `preimage_eq_top_of_surjective (pullback.fst V.hom p)` to reduce the goal to its premises. Rewrite using `[← map_left_fst p g, ← h, map_left_fst p f, Scheme.Hom.comp_preimage, hf, Scheme.Hom.preimage_top]`.
-/
private theorem preimage_eq_univ_of_pullback_map_eq {S S' : Scheme.{0}} (p : S' ⟶ S) [Surjective p] {V W : Over S}
    (f g : V ⟶ W) (h : (Over.pullback p).map f = (Over.pullback p).map g) (U : W.left.Opens)
    (hf : f.left ⁻¹ᵁ U = ⊤) : g.left ⁻¹ᵁ U = ⊤ := by
  apply preimage_eq_top_of_surjective (pullback.fst V.hom p)
  rw [← map_left_fst p g, ← h, map_left_fst p f, Scheme.Hom.comp_preimage, hf,
    Scheme.Hom.preimage_top]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW`. Take `⟨g0, d0, hg0, hd0⟩` from `exists_factor_through_quotient_of_surjective J β hβ hker`. Establish `hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = Spec.map g0 ≫ Spec.map β`.

Rewrite using `[← hg0, Spec.map_comp]`. Establish `hp : Spec.map β = Spec.map d0 ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`. Rewrite using `[← hd0, Spec.map_comp]`. Establish `hJ2 : J ^ 2 = ⊥`. Rewrite `hJ` using `[pow_one]`.

Rewrite using `[hJ, pow_two, Ideal.mul_bot]`. Take `⟨f', hf'1, hf'2⟩` from `GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A J hJ2 X G f ((pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f f).2.1 hf)`. Conclude with `⟨f', hf'1, (pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f' f).1.2 hf'2⟩`. Consider the case `succ n ih`. Introduce `A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW`.

Take `⟨I, hIdef⟩ : ∃ I : Ideal A, I = J ^ (n + 1)` from `⟨_, rfl⟩`. Establish `hI2 : I ^ 2 = ⊥`. Rewrite using `[eq_bot_iff, ← hJ, hIdef, ← pow_mul]`. Conclude with `Ideal.pow_le_pow_right (by omega)`. Establish `hIJ : I ≤ J` using `hIdef ▸ Ideal.pow_le_self (by omega)`.

Establish `hItop : I ≠ ⊤`. Introduce `h`. Rewrite `hI2` using `[h, pow_two, Ideal.top_mul]`. Conclude with `top_ne_bot hI2`. Establish `: Nontrivial (A ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 hItop`.

Establish `: IsLocalRing (A ⧸ I)` using `.of_surjective' _ Ideal.Quotient.mk_surjective`. Establish `hIker : I ≤ RingHom.ker β.hom` using `hker ▸ hIJ`. Set `β' : CommRingCat.of (A ⧸ I) ⟶ C` to `CommRingCat.ofHom (Ideal.Quotient.lift I β.hom (fun a ha => (RingHom.mem_ker).1 (hIker ha)))`. Establish `hββ : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ β' = β`. Use extensionality with `a`.

Both sides reduce to the same expression. Establish `hβ' : Function.Surjective β'`. Introduce `c`. Take `⟨a, rfl⟩` from `hβ c`. Conclude with `⟨Ideal.Quotient.mk I a, rfl⟩`.

Establish `hker' : RingHom.ker β'.hom = J.map (Ideal.Quotient.mk I)`. Simplify using `only [β', CommRingCat.hom_ofHom]`. Rewrite using `[← hker]`. Conclude with `Ideal.ker_quotient_lift _ hIker`. Establish `hJ' : (J.map (Ideal.Quotient.mk I)) ^ (n + 1) = ⊥`.

Rewrite using `[← Ideal.map_pow, ← hIdef, Ideal.map_quotient_self]`. Establish `hSpec : Spec.map β = Spec.map β' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Rewrite using `[← hββ, Spec.map_comp]`. Establish `hsurjβ' : Surjective (Spec.map β')` using `surjective_specMap β' hβ' ⟨n + 1, by rw [hker', hJ', Ideal.zero_eq_bot]⟩`. Establish `hInil : IsNilpotent I` using `⟨2, by rw [hI2, Ideal.zero_eq_bot]⟩`.

Establish `: Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).hom` using `by show Smooth (pullback.snd G.hom _) infer_instance`. Take `⟨e, he, -⟩` from `GlobalTheory.splitTorus_baseChange (Spec (CommRingCat.of A)) (Spec (CommRingCat.of (A ⧸ I))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X`. Take `⟨f₁, hf₁def⟩ : ∃ f₁, f₁ = e.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f` from `⟨_, rfl⟩`. Set `W' : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).left.Opens` to `pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ W`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`.

Establish `: IsClosedImmersion (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))` using `inferInstance`. Establish `hW' : IsAffineOpen W'` using `hW.preimage _`. Establish `hf₁W : f₁.left ⁻¹ᵁ W' = ⊤`. Establish `h1 : f₁.left ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) = (e.hom.left ≫ pullback.fst _ _) ≫ f.left`. Rewrite using `[hf₁def, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]`.

Express the relevant statement in the definitionally equal form `(f₁.left ≫ pullback.fst G.hom _) ⁻¹ᵁ W = ⊤`. Rewrite using `[h1, Scheme.Hom.comp_preimage, hfW, Scheme.Hom.preimage_top]`. Establish `hf₁ : IsMonHom ((Over.pullback (Spec.map β')).map f₁)`. Establish `h2 : IsMonHom ((Over.pullback (Spec.map β')).map ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f))` using `(isMonHom_map_iff hSpec f).1 hf`. Rewrite using `[hf₁def, Functor.map_comp]`.

Use `infer_instance`. Take `⟨f₂, hf₂, hf₂eq⟩` from `ih (A ⧸ I) (J.map (Ideal.Quotient.mk I)) hJ' β' hβ' hker' ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G) f₁ hf₁ W' hW' hf₁W`. Establish `hf₂W : f₂.left ⁻¹ᵁ W' = ⊤` using `preimage_eq_univ_of_pullback_map_eq (Spec.map β') f₁ f₂ hf₂eq.symm W' hf₁W`. Take `⟨F, -, hF⟩` from `exists_lift I hInil X G (e.inv ≫ f₂) hW (by`. Express the relevant statement in the definitionally equal form `e.inv.left ⁻¹ᵁ (f₂.left ⁻¹ᵁ W') = ⊤`.

Rewrite using `[hf₂W]`. Use the proof step `rfl)`. Establish `hFmon : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map F)`. Rewrite using `[hF]`. Use `infer_instance`.

Take `⟨F', hF'1, hF'2⟩` from `GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A I hI2 X G F hFmon`. Use `⟨F', hF'1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_eq_iff hSpec, hF'2, hF, Functor.map_comp, hf₂eq, hf₁def, Functor.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]`.
-/
private theorem exists_isMonHom_lift_of_isMonHom_baseChange (X : Type) [AddCommGroup X] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), J ^ (n + 1) = ⊥ →
      ∀ {C : CommRingCat.{0}} (β : CommRingCat.of A ⟶ C), Function.Surjective β →
      RingHom.ker β.hom = J → ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
        [Smooth G.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  induction n with
  | zero =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨g0, d0, hg0, hd0⟩ := exists_factor_through_quotient_of_surjective J β hβ hker
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = Spec.map g0 ≫ Spec.map β := by
      rw [← hg0, Spec.map_comp]
    have hp : Spec.map β = Spec.map d0 ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [← hd0, Spec.map_comp]
    have hJ2 : J ^ 2 = ⊥ := by
      rw [pow_one] at hJ
      rw [hJ, pow_two, Ideal.mul_bot]
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A J hJ2 X G f
      ((pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f f).2.1 hf)
    exact ⟨f', hf'1, (pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f' f).1.2 hf'2⟩
  | succ n ih =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal A, I = J ^ (n + 1) := ⟨_, rfl⟩
    have hI2 : I ^ 2 = ⊥ := by
      rw [eq_bot_iff, ← hJ, hIdef, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    have hIJ : I ≤ J := hIdef ▸ Ideal.pow_le_self (by omega)
    have hItop : I ≠ ⊤ := by
      intro h
      rw [h, pow_two, Ideal.top_mul] at hI2
      exact top_ne_bot hI2
    have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
    have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hIker : I ≤ RingHom.ker β.hom := hker ▸ hIJ
    let β' : CommRingCat.of (A ⧸ I) ⟶ C :=
      CommRingCat.ofHom (Ideal.Quotient.lift I β.hom (fun a ha => (RingHom.mem_ker).1 (hIker ha)))
    have hββ : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ β' = β := by
      ext a
      rfl
    have hβ' : Function.Surjective β' := by
      intro c
      obtain ⟨a, rfl⟩ := hβ c
      exact ⟨Ideal.Quotient.mk I a, rfl⟩
    have hker' : RingHom.ker β'.hom = J.map (Ideal.Quotient.mk I) := by
      simp only [β', CommRingCat.hom_ofHom]
      rw [← hker]
      exact Ideal.ker_quotient_lift _ hIker
    have hJ' : (J.map (Ideal.Quotient.mk I)) ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow, ← hIdef, Ideal.map_quotient_self]
    have hSpec : Spec.map β = Spec.map β' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [← hββ, Spec.map_comp]
    have hsurjβ' : Surjective (Spec.map β') :=
      surjective_specMap β' hβ' ⟨n + 1, by rw [hker', hJ', Ideal.zero_eq_bot]⟩
    have hInil : IsNilpotent I := ⟨2, by rw [hI2, Ideal.zero_eq_bot]⟩
    have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).hom := by
      show Smooth (pullback.snd G.hom _)
      infer_instance
    obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Spec (CommRingCat.of A))
      (Spec (CommRingCat.of (A ⧸ I))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X
    obtain ⟨f₁, hf₁def⟩ : ∃ f₁, f₁ = e.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f := ⟨_, rfl⟩
    let W' : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).left.Opens :=
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ W
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :=
      inferInstance
    have hW' : IsAffineOpen W' := hW.preimage _
    have hf₁W : f₁.left ⁻¹ᵁ W' = ⊤ := by
      have h1 : f₁.left ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
          (e.hom.left ≫ pullback.fst _ _) ≫ f.left := by
        rw [hf₁def, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
      change (f₁.left ≫ pullback.fst G.hom _) ⁻¹ᵁ W = ⊤
      rw [h1, Scheme.Hom.comp_preimage, hfW, Scheme.Hom.preimage_top]
    have hf₁ : IsMonHom ((Over.pullback (Spec.map β')).map f₁) := by
      have h2 : IsMonHom ((Over.pullback (Spec.map β')).map
          ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f)) :=
        (isMonHom_map_iff hSpec f).1 hf
      rw [hf₁def, Functor.map_comp]
      infer_instance
    obtain ⟨f₂, hf₂, hf₂eq⟩ := ih (A ⧸ I) (J.map (Ideal.Quotient.mk I)) hJ' β' hβ' hker'
      ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G) f₁ hf₁ W' hW' hf₁W
    have hf₂W : f₂.left ⁻¹ᵁ W' = ⊤ := preimage_eq_univ_of_pullback_map_eq (Spec.map β') f₁ f₂ hf₂eq.symm W' hf₁W
    obtain ⟨F, -, hF⟩ := exists_lift I hInil X G (e.inv ≫ f₂) hW (by
      change e.inv.left ⁻¹ᵁ (f₂.left ⁻¹ᵁ W') = ⊤
      rw [hf₂W]
      rfl)
    have hFmon : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map F) := by
      rw [hF]
      infer_instance
    obtain ⟨F', hF'1, hF'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A I hI2 X G F hFmon
    refine ⟨F', hF'1, ?_⟩
    rw [map_eq_iff hSpec, hF'2, hF, Functor.map_comp, hf₂eq, hf₁def, Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/- English proof (translation)
Introduce `_ hloc C β hβ hker G _ _ _ f hf W hW hfW`. Take `⟨n, hn⟩` from `hJ`. Consider the cases of `n with`. Consider the case `zero`. It suffices to derive a contradiction.

Rewrite `hn` using `[pow_zero, Ideal.one_eq_top, Ideal.zero_eq_bot]`. Conclude with `top_ne_bot hn`. Consider the case `succ n`. Conclude with `exists_isMonHom_lift_of_isMonHom_baseChange X n A J (by rw [hn, Ideal.zero_eq_bot]) β hβ hker G f hf W hW hfW`.
-/
theorem exists_correction {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] : IsNilpotent J → IsLocalRing A → ∀ {C : CommRingCat.{0}}
      (β : CommRingCat.of A ⟶ C), Function.Surjective β → RingHom.ker β.hom = J →
      ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
        (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  intro _ hloc C β hβ hker G _ _ _ f hf W hW hfW
  obtain ⟨n, hn⟩ := hJ
  cases n with
  | zero =>
    exfalso
    rw [pow_zero, Ideal.one_eq_top, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  | succ n =>
    exact exists_isMonHom_lift_of_isMonHom_baseChange X n A J (by rw [hn, Ideal.zero_eq_bot]) β hβ hker G f hf W hW hfW

/- English proof (translation)
Establish `hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` using `surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)`. Set `i` to `pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `: IsClosedImmersion i` using `inferInstanceAs (IsClosedImmersion (pullback.fst _ _))`. Establish `hemb : Topology.IsClosedEmbedding i.base` using `i.isClosedEmbedding`.

Establish `hbij : Function.Bijective i.base` using `⟨hemb.injective, i.surjective⟩`. Establish `hopen : IsOpen (i.base '' (W : Set _))`. Rewrite using `[← compl_compl (i.base '' (W : Set _)), ← Set.image_compl_eq hbij]`. Conclude with `(hemb.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl`. Set `U : G.left.Opens` to `⟨_, hopen⟩`.

Establish `hU : i ⁻¹ᵁ U = W`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `i.base x ∈ i.base '' (W : Set _) ↔ x ∈ W`. Conclude with `hemb.injective.mem_set_image`. Use `⟨U, ?_, hU⟩` and prove the remaining obligations.

Establish `hW' : IsAffineOpen (i ⁻¹ᵁ U)` using `hU ▸ hW`. Establish `: IsAffine (pullback (U.ι ≫ G.hom) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))`. Establish `: IsAffine (i ⁻¹ᵁ U)` using `hW'`. Apply the tactic sequence `exact IsAffine.of_isIso ((pullbackRightPullbackFstIso G.hom _ U.ι).inv ≫ (pullbackSymmetry _ _).hom ≫ (pullbackRestrictIsoRestrict i U).hom)`. Conclude with `GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent A J hJ (Over.mk (U.ι ≫ G.hom)) this`.
-/
theorem exists_affineOpen {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G : Over (Spec (CommRingCat.of A)))
    (W : (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).Opens)
    (hW : IsAffineOpen W) : ∃ U : G.left.Opens, IsAffineOpen U ∧
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ U = W := by
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  let i := pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have hemb : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  have hbij : Function.Bijective i.base := ⟨hemb.injective, i.surjective⟩
  have hopen : IsOpen (i.base '' (W : Set _)) := by
    rw [← compl_compl (i.base '' (W : Set _)), ← Set.image_compl_eq hbij]
    exact (hemb.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl
  let U : G.left.Opens := ⟨_, hopen⟩
  have hU : i ⁻¹ᵁ U = W := by
    ext x
    change i.base x ∈ i.base '' (W : Set _) ↔ x ∈ W
    exact hemb.injective.mem_set_image
  refine ⟨U, ?_, hU⟩
  have hW' : IsAffineOpen (i ⁻¹ᵁ U) := hU ▸ hW
  have : IsAffine (pullback (U.ι ≫ G.hom) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    have : IsAffine (i ⁻¹ᵁ U) := hW'
    exact IsAffine.of_isIso ((pullbackRightPullbackFstIso G.hom _ U.ι).inv ≫
      (pullbackSymmetry _ _).hom ≫ (pullbackRestrictIsoRestrict i U).hom)
  exact GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent A J hJ (Over.mk (U.ι ≫ G.hom)) this

/- English proof (translation)
Introduce `A _ _ J hJ X _ G _ _ _ i₀ hi₀ ⟨W, hW, hW0⟩`. Take `⟨U, hU, hUW⟩` from `exists_affineOpen J hJ G W hW`. Take `⟨f, hfU, hf⟩` from `exists_lift J hJ X G i₀ hU (by`. Rewrite using `[Scheme.Hom.comp_preimage, hUW]`. Conclude with `hW0)`.

Take `⟨f', hf'1, hf'2⟩` from `exists_correction J hJ X hJ inferInstance (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective (by simp) G f (by rw [hf]; exact hi₀) U hU hfU`. Use `⟨f', ⟨hf'1, hf'2.trans hf⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `i ⟨hi1, hi2⟩`. Use `open CategoryTheory.GrpObj in`. Establish `hmon : IsMonHom (i * f'⁻¹)`.

Rewrite using `[Hom.mul_def]`. Use `infer_instance`. Use `open CategoryTheory.GrpObj in`. Establish `hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (i * f'⁻¹) = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (toUnit _ ≫ η[G])`. Rewrite using `[Functor.map_mul, Functor.map_inv', hi2, hf'2, hf, mul_inv_cancel, ← Hom.one_def, Functor.map_one]`.

Use `open CategoryTheory.GrpObj in`. Establish `key` using `GlobalTheory.splitTorus_hom_eq_one_of_nilpotent A J hJ X G (i * f'⁻¹) hmon hmap`. Use `open CategoryTheory.GrpObj in`. Rewrite `key` using `[← Hom.one_def, mul_inv_eq_one]`. Conclude with `key`.
-/
theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (i₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G), IsMonHom i₀ → (∃ W : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤) → ∃! i : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom i ∧ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map i = i₀ := by
  intro A _ _ J hJ X _ G _ _ _ i₀ hi₀ ⟨W, hW, hW0⟩
  obtain ⟨U, hU, hUW⟩ := exists_affineOpen J hJ G W hW
  obtain ⟨f, hfU, hf⟩ := exists_lift J hJ X G i₀ hU (by
    rw [Scheme.Hom.comp_preimage, hUW]
    exact hW0)
  obtain ⟨f', hf'1, hf'2⟩ := exists_correction J hJ X hJ inferInstance
    (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective (by simp) G f
    (by rw [hf]; exact hi₀) U hU hfU
  refine ⟨f', ⟨hf'1, hf'2.trans hf⟩, ?_⟩
  rintro i ⟨hi1, hi2⟩
  open CategoryTheory.GrpObj in
  have hmon : IsMonHom (i * f'⁻¹) := by
    rw [Hom.mul_def]
    infer_instance
  open CategoryTheory.GrpObj in
  have hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (i * f'⁻¹) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (toUnit _ ≫ η[G]) := by
    rw [Functor.map_mul, Functor.map_inv', hi2, hf'2, hf, mul_inv_cancel, ← Hom.one_def, Functor.map_one]
  open CategoryTheory.GrpObj in
  have key := GlobalTheory.splitTorus_hom_eq_one_of_nilpotent A J hJ X G (i * f'⁻¹) hmon hmap
  open CategoryTheory.GrpObj in
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory.TorusLift
