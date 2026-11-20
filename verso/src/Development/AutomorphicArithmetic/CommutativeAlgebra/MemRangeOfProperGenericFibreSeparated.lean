import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSpecializesLiftGenericBaseChange

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy`. Use `set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg`. Set `U' : Y.Opens` to `π ⁻¹ᵁ ι.opensRange`. Establish `hjU : Set.range j ⊆ Set.range U'.ι`. Introduce and unpack `_ ⟨d, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Use `show π (j d) ∈ ι.opensRange`. Rewrite using `[← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Set `jU : D ⟶ U'` to `IsOpenImmersion.lift U'.ι j hjU`.

Establish `hjUf : jU ≫ U'.ι = j` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `z.2`. Set `w : (U' : Scheme) ⟶ Sp R` to `IsOpenImmersion.lift ι (U'.ι ≫ π) hπU`.

Establish `hw : w ≫ ι = U'.ι ≫ π` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hjw : jU ≫ w = q`. Rewrite using `[← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]`. Use `haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance`. Use `haveI : IsSeparated w := IsSeparated.of_comp w ι`.

Set `m : C ⟶ pullback w g` to `pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])`. Establish `hm : m ≫ pullback.snd w g = c` using `pullback.lift_snd _ _ _`. Use `haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance`. Use `haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)`. Establish `hleft : IsPullback m v (pullback.fst w g) jU`.

Use `IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip` and prove the remaining obligations. Rewrite using `[hm, hjw]`. Conclude with `hpb.flip`. Establish `hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU` using `(Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm`. Establish `hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m`.

Introduce `z hz`. Establish `e` using `IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)`. Establish `hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU)`. Rewrite using `[e]`. Conclude with `hz`.

Take `⟨t, rfl⟩` from `hz'`. Use `⟨hleft.isoPullback.inv t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hI]`. Take `⟨p, hp⟩` from `hy`. Establish `hyU : y ∈ U'` using `by show π y ∈ ι.opensRange`.

Rewrite using `[← hp, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Set `yU : U'` to `⟨y, hyU⟩`. Establish `e1 : ι (w yU) = π y` using `by show (w ≫ ι) yU = π y`. Rewrite using `[hw]`.

Both sides reduce to the same expression. Establish `hwy : w yU = g p`. Apply `ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[e1, ← hp]`. Both sides reduce to the same expression.

Take `⟨y', hy'1, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy`. Establish `hξ : genericPoint Y ∈ Set.range j`. Rewrite using `[(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]`. Conclude with `hd.nonempty`. Take `⟨d, hdξ⟩` from `hξ`.

Establish `hsp : jU d ⤳ yU`. Apply `(U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp` to reduce the goal to its premises. Establish `e2 : U'.ι (jU d) = genericPoint Y`. Rewrite using `[← Scheme.Hom.comp_apply, hjUf, hdξ]`. Rewrite using `[e2]`.

Conclude with `(genericPoint_spec Y).specializes (Set.mem_univ _)`. Take `⟨x', hx'sp, hx'fst⟩` from `UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)`. Establish `hx'm : x' ∈ Set.range m` using `hrange ⟨d, hx'fst.symm⟩`. Establish `hy'm : y' ∈ Set.range m` using `hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm`. Take `⟨c0, hc0⟩` from `hy'm`.

Use `⟨v c0, ?_⟩` and prove the remaining obligations. Establish `h1 : pullback.fst w g (m c0) = jU (v c0)`. Rewrite using `[← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]`. Rewrite using `[← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.mem_range_of_proper_generic_fibre_separated :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {B Y D C : Scheme.{0}} (ι : Sp R ⟶ B) [IsOpenImmersion ι] (π : Y ⟶ B) [IsSeparated π] [IrreducibleSpace Y] (j : D ⟶ Y) [IsOpenImmersion j], Dense (Set.range j) → ∀ (q : D ⟶ Sp R), j ≫ π = q ≫ ι → ∀ (c : C ⟶ Sp Ω) [IsProper c] (v : C ⟶ D), IsPullback v c q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) → ∀ (y : Y), π y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) → y ∈ Set.range j := by
  intro R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy
  set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg
  let U' : Y.Opens := π ⁻¹ᵁ ι.opensRange
  have hjU : Set.range j ⊆ Set.range U'.ι := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    show π (j d) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let jU : D ⟶ U' := IsOpenImmersion.lift U'.ι j hjU
  have hjUf : jU ≫ U'.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let w : (U' : Scheme) ⟶ Sp R := IsOpenImmersion.lift ι (U'.ι ≫ π) hπU
  have hw : w ≫ ι = U'.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hjw : jU ≫ w = q := by
    rw [← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]
  haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance
  haveI : IsSeparated w := IsSeparated.of_comp w ι
  let m : C ⟶ pullback w g := pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])
  have hm : m ≫ pullback.snd w g = c := pullback.lift_snd _ _ _
  haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance
  haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)
  have hleft : IsPullback m v (pullback.fst w g) jU := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip
    rw [hm, hjw]
    exact hpb.flip
  have hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU :=
    (Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm
  have hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m := by
    intro z hz
    have e := IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)
    have hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU) := by
      rw [e]
      exact hz
    obtain ⟨t, rfl⟩ := hz'
    refine ⟨hleft.isoPullback.inv t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hI]
  obtain ⟨p, hp⟩ := hy
  have hyU : y ∈ U' := by
    show π y ∈ ι.opensRange
    rw [← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let yU : U' := ⟨y, hyU⟩
  have e1 : ι (w yU) = π y := by
    show (w ≫ ι) yU = π y
    rw [hw]
    rfl
  have hwy : w yU = g p := by
    apply ι.isOpenEmbedding.injective
    rw [e1, ← hp]
    rfl
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy
  have hξ : genericPoint Y ∈ Set.range j := by
    rw [(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]
    exact hd.nonempty
  obtain ⟨d, hdξ⟩ := hξ
  have hsp : jU d ⤳ yU := by
    apply (U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    have e2 : U'.ι (jU d) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, hjUf, hdξ]
    rw [e2]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', hx'sp, hx'fst⟩ := UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)
  have hx'm : x' ∈ Set.range m := hrange ⟨d, hx'fst.symm⟩
  have hy'm : y' ∈ Set.range m := hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm
  obtain ⟨c0, hc0⟩ := hy'm
  refine ⟨v c0, ?_⟩
  have h1 : pullback.fst w g (m c0) = jU (v c0) := by
    rw [← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]
  rw [← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]
  rfl
