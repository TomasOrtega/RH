import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IsGaloisCover

/- English proof (translation)
Set `k` to `T.residueField p`. Set `K` to `AlgebraicClosure k`. Set `i : Spec (CommRingCat.of K) ⟶ Spec k` to `Spec.map (CommRingCat.ofHom (algebraMap k K))`. Use `⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩` and prove the remaining obligations. Take `⟨z⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p)` using `⟨_, rfl⟩`. Rewrite `hz` using `[Scheme.range_fromSpecResidueField]`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `Set.mem_singleton_iff.mp hz`.
-/
theorem exists_algClosed_point (T : Scheme.{0}) (p : T) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : Sp K ⟶ T), p ∈ Set.range j := by
  let k := T.residueField p
  let K := AlgebraicClosure k
  let i : Spec (CommRingCat.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨z, ?_⟩
  have hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hz
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp hz

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}

/- English proof (translation)
Use `h.etale` as an intermediate fact. Set `D` to `pullback.diagonal π`. Set `m : Ga → (T ⟶ pullback π π)` to `fun a => pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])`. Take `⟨K, _, _, j, z, hz⟩` from `exists_algClosed_point T p`. Take `⟨a, ha, -⟩` from `h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])`.

Establish `hm1 : m a ≫ pullback.fst π π = x ≫ ρ a` using `pullback.lift_fst _ _ _`. Establish `hm2 : m a ≫ pullback.snd π π = x'` using `pullback.lift_snd _ _ _`. Establish `hjm : j ≫ m a = j ≫ x' ≫ D`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]`.

Simplify `ha` using `only [Category.assoc]`. Rewrite using `[Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]`. Set `V : T.Opens` to `(m a) ⁻¹ᵁ D.opensRange`. Establish `hpV : p ∈ V` using `by show (m a) p ∈ Set.range D`. Rewrite using `[← hz]`.

Use `⟨x' (j z), ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]`. Establish `hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw : V.ι w ∈ (V : Set T)`.

Rewrite using `[← Scheme.Opens.range_ι V]`. Conclude with `⟨w, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hw`. Set `l` to `IsOpenImmersion.lift D (V.ι ≫ m a) hsub`.

Establish `hl : l ≫ D = V.ι ≫ m a` using `IsOpenImmersion.lift_fac _ _ _`. Use `⟨V, a, hpV, ?_⟩` and prove the remaining obligations. Establish `e1 : V.ι ≫ x ≫ ρ a = l`. Establish `h1 : l ≫ D ≫ pullback.fst π π = l` using `by rw [pullback.diagonal_fst, Category.comp_id]`. Rewrite using `[← h1, ← Category.assoc l, hl, Category.assoc, hm1]`.

Establish `e2 : V.ι ≫ x' = l`. Establish `h2 : l ≫ D ≫ pullback.snd π π = l` using `by rw [pullback.diagonal_snd, Category.comp_id]`. Rewrite using `[← h2, ← Category.assoc l, hl, Category.assoc, hm2]`. Rewrite using `[e1, e2]`.
-/
theorem exists_local_geom (h : IsGaloisCover Ga ρ π) {T : Scheme.{0}} (x x' : T ⟶ X) (hx : x ≫ π = x' ≫ π) (p : T) :
    ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  have := h.etale
  let D := pullback.diagonal π
  let m : Ga → (T ⟶ pullback π π) := fun a =>
    pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])
  obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point T p
  obtain ⟨a, ha, -⟩ := h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])
  have hm1 : m a ≫ pullback.fst π π = x ≫ ρ a := pullback.lift_fst _ _ _
  have hm2 : m a ≫ pullback.snd π π = x' := pullback.lift_snd _ _ _
  have hjm : j ≫ m a = j ≫ x' ≫ D := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      simpa only [Category.assoc] using ha
    · rw [Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  let V : T.Opens := (m a) ⁻¹ᵁ D.opensRange
  have hpV : p ∈ V := by
    show (m a) p ∈ Set.range D
    rw [← hz]
    refine ⟨x' (j z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]
  have hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  let l := IsOpenImmersion.lift D (V.ι ≫ m a) hsub
  have hl : l ≫ D = V.ι ≫ m a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, a, hpV, ?_⟩
  have e1 : V.ι ≫ x ≫ ρ a = l := by
    have h1 : l ≫ D ≫ pullback.fst π π = l := by rw [pullback.diagonal_fst, Category.comp_id]
    rw [← h1, ← Category.assoc l, hl, Category.assoc, hm1]
  have e2 : V.ι ≫ x' = l := by
    have h2 : l ≫ D ≫ pullback.snd π π = l := by rw [pullback.diagonal_snd, Category.comp_id]
    rw [← h2, ← Category.assoc l, hl, Category.assoc, hm2]
  rw [e1, e2]

/- English proof (translation)
Use `h.fin` as an intermediate fact. Use `h.etale` as an intermediate fact. Use `h.onto` as an intermediate fact. Establish `key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f`. Introduce `W g₁ g₂ hg`.

Apply `Scheme.hom_ext_of_forall` to reduce the goal to its premises. Introduce `p`. Take `⟨V, a, hp, hV⟩` from `h.exists_local_geom g₁ g₂ hg p`. Use `⟨V, hp, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩` and prove the remaining obligations. Introduce `f' hf'`. Apply `(cancel_epi π).1` to reduce the goal to its premises. Rewrite using `[hf', EffectiveEpi.fac]`.
-/
theorem existsUnique_desc (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]

variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

/- English proof (translation)
Establish `hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π`. Simplify using `only [Category.assoc, hp.w, reassoc_of% hy]`. Take `⟨a, ha, hauniq⟩` from `h.fibre K (y ≫ u) (y' ≫ u) hyu`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Apply `hp.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hu, ← Category.assoc, ha]`. Rewrite using `[Category.assoc, hπ, hy]`. Introduce `b hb`. Apply `hauniq` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← hu, ← Category.assoc, hb]`.
-/
private theorem existsUnique_act_of_isPullback_isGaloisCover (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a) (hπ : ∀ a, ρ' a ≫ π' = π') (K : Type) [Field K] [IsAlgClosed K]
    (y y' : Sp K ⟶ X') (hy : y ≫ π' = y' ≫ π') : ∃! a, y ≫ ρ' a = y' := by
  have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
    simp only [Category.assoc, hp.w, reassoc_of% hy]
  obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
  refine ⟨a, ?_, ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hu, ← Category.assoc, ha]
    · rw [Category.assoc, hπ, hy]
  · intro b hb
    apply hauniq
    rw [Category.assoc, ← hu, ← Category.assoc, hb]

/- English proof (translation)
Use `h.fin` as an intermediate fact. Use `h.etale` as an intermediate fact. Use `h.onto` as an intermediate fact. Use `h'.fin` as an intermediate fact. Use `h'.etale` as an intermediate fact.

Set `ρP : Ga → (pullback π v ⟶ pullback π v)` to `fun a => pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])`. Establish `huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a` using `fun a => pullback.lift_fst _ _ _`. Establish `hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v` using `fun a => by`. Rewrite using `[← Category.comp_id (pullback.snd π v)]`. Conclude with `pullback.lift_snd _ _ _`.

Set `φ : X' ⟶ pullback π v` to `pullback.lift u π' w`. Establish `hφ1 : φ ≫ pullback.fst π v = u` using `pullback.lift_fst _ _ _`. Establish `hφ2 : φ ≫ pullback.snd π v = π'` using `pullback.lift_snd _ _ _`. Establish `hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ` using `fun a => by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]`. Simplify using `only [Category.assoc, hπP, hφ2, h'.inv]`. Establish `hmono : Mono φ`. Prove the components needed by the constructor for the conclusion. Introduce `T g₁ g₂ hg`.

Establish `hg1 : g₁ ≫ u = g₂ ≫ u` using `by rw [← hφ1, reassoc_of% hg]`. Establish `hg2 : g₁ ≫ π' = g₂ ≫ π'` using `by rw [← hφ2, reassoc_of% hg]`. Apply `Scheme.hom_ext_of_forall` to reduce the goal to its premises. Introduce `p`. Take `⟨V, a, hp, hV⟩` from `h'.exists_local_geom g₁ g₂ hg2 p`.

Use `⟨V, hp, ?_⟩` and prove the remaining obligations. Establish `e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u`. Rewrite using `[← hu, hg1]`. Simplify `congrArg (· ≫ u) hV` using `only [Category.assoc]`. Take `⟨K, _, _, j, -⟩` from `exists_algClosed_point V.toScheme ⟨p, hp⟩`.

Establish `ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u`. Simplify using `only [Category.assoc] at e ⊢`. Rewrite using `[e]`. Establish `h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u`. Rewrite using `[h.one, Category.comp_id]`.

Establish `ha1 : a = 1` using `(h.fibre K _ _ rfl).unique ha h1`. Rewrite using `[← hV, ha1, h'.one, Category.comp_id]`. Establish `hsurj : Surjective φ`. Prove the components needed by the constructor for the conclusion. Introduce `q`.

Take `⟨y, hy⟩` from `h'.onto.surj (pullback.snd π v q)`. Take `⟨r, hr1, hr2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v) (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])`. Take `⟨K, _, _, j, z, hz⟩` from `exists_algClosed_point _ r`. Take `⟨a, ha, -⟩` from `existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _) (by simp only [Category.assoc, pullback.condition])`. Use `⟨ρ' a y, ?_⟩` and prove the remaining obligations.

Establish `hz'` using `congrArg (fun m : Sp K ⟶ _ => m z) ha`. Simplify using `only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'`. Rewrite using `[← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]`. Conclude with `hz'`. Establish `: Etale φ`.

Establish `: Etale (φ ≫ pullback.snd π v)` using `by rw [hφ2]; exact h'.etale`. Conclude with `Etale.of_comp (f := φ) (pullback.snd π v)`. Establish `: QuasiCompact φ`. Establish `: QuasiCompact (φ ≫ pullback.snd π v)` using `by rw [hφ2]; infer_instance`. Conclude with `MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ (pullback.snd π v) inferInstance this`.

Establish `: IsIso φ` using `Flat.isIso_of_surjective_of_mono φ`. Conclude with `IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2`.
-/
theorem isPullback (h : IsGaloisCover Ga ρ π) (h' : IsGaloisCover Ga ρ' π') (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (w : u ≫ π = π' ≫ v) : IsPullback u π' π v := by
  have := h.fin
  have := h.etale
  have := h.onto
  have := h'.fin
  have := h'.etale
  let ρP : Ga → (pullback π v ⟶ pullback π v) := fun a =>
    pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])
  have huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a := fun a => pullback.lift_fst _ _ _
  have hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v := fun a => by
    rw [← Category.comp_id (pullback.snd π v)]
    exact pullback.lift_snd _ _ _
  let φ : X' ⟶ pullback π v := pullback.lift u π' w
  have hφ1 : φ ≫ pullback.fst π v = u := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π v = π' := pullback.lift_snd _ _ _
  have hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ := fun a => by
    apply pullback.hom_ext
    · simp only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]
    · simp only [Category.assoc, hπP, hφ2, h'.inv]
  have hmono : Mono φ := by
    constructor
    intro T g₁ g₂ hg
    have hg1 : g₁ ≫ u = g₂ ≫ u := by rw [← hφ1, reassoc_of% hg]
    have hg2 : g₁ ≫ π' = g₂ ≫ π' := by rw [← hφ2, reassoc_of% hg]
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h'.exists_local_geom g₁ g₂ hg2 p
    refine ⟨V, hp, ?_⟩
    have e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u := by
      rw [← hu, hg1]
      simpa only [Category.assoc] using congrArg (· ≫ u) hV
    obtain ⟨K, _, _, j, -⟩ := exists_algClosed_point V.toScheme ⟨p, hp⟩
    have ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u := by
      simp only [Category.assoc] at e ⊢
      rw [e]
    have h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u := by
      rw [h.one, Category.comp_id]
    have ha1 : a = 1 := (h.fibre K _ _ rfl).unique ha h1
    rw [← hV, ha1, h'.one, Category.comp_id]
  have hsurj : Surjective φ := by
    constructor
    intro q
    obtain ⟨y, hy⟩ := h'.onto.surj (pullback.snd π v q)
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v)
      (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])
    obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point _ r
    obtain ⟨a, ha, -⟩ := existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K
      (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
    refine ⟨ρ' a y, ?_⟩
    have hz' := congrArg (fun m : Sp K ⟶ _ => m z) ha
    simp only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'
    rw [← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]
    exact hz'
  have : Etale φ := by
    have : Etale (φ ≫ pullback.snd π v) := by rw [hφ2]; exact h'.etale
    exact Etale.of_comp (f := φ) (pullback.snd π v)
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ pullback.snd π v) := by rw [hφ2]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ
      (pullback.snd π v) inferInstance this
  have : IsIso φ := Flat.isIso_of_surjective_of_mono φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2

/- English proof (translation)
The claim follows from `h.finite one := by apply hp.hom_ext · rw [hu 1, h.one, Category.id_comp, Category.comp_id] · rw [hπ 1, Category.id_comp] mul := by intro a c apply hp.hom_ext · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)] · rw [hπ, Category.assoc, hπ c, hπ a] inv := hπ fin := by have …`.
-/
theorem of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' where
  finite := h.finite
  one := by
    apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  mul := by
    intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  inv := hπ
  fin := by
    have := h.fin
    exact MorphismProperty.of_isPullback hp h.fin
  etale := by
    have := h.etale
    exact MorphismProperty.of_isPullback hp h.etale
  onto := by
    have := h.onto
    exact MorphismProperty.of_isPullback hp h.onto
  fibre := by
    intro K _ _ y y' hy
    have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
      simp only [Category.assoc, hp.w]
      simp only [← Category.assoc, hy]
    obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
    refine ⟨a, ?_, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, hu, ← Category.assoc, ha]
      · rw [Category.assoc, hπ, hy]
    · intro b hb
      apply hauniq
      rw [Category.assoc, ← hu, ← Category.assoc, hb]

end GlobalTheory.ZM.IsGaloisCover

namespace GlobalTheory.ZM

/- English proof (translation)
Introduce `X Y π Ga _ ρ h`. Use `⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩` and prove the remaining obligations. Introduce `X' Y' π' ρ' u v hu w`. Conclude with `⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩`.
-/
theorem galoisCover_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩

end GlobalTheory.ZM
