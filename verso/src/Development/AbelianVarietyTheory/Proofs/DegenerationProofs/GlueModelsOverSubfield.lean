import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueModels

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Set `T : Bool → Scheme.{0}` to `fun i => Bool.rec U V i`. Set `t : ∀ i, T i ⟶ X` to `fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i`. Set `m : ∀ i, T i ⟶ Y` to `fun i => Bool.rec (motive := fun i => T i ⟶ Y) a b i`. Apply the tactic sequence `have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption`. Set `𝒰 : X.OpenCover` to `Scheme.Cover.mkOfCovers Bool T t (fun x => by`.

Break down `hc x with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases. Conclude with `⟨false, y, hy⟩`. Conclude with `⟨true, y, hy⟩)`. It suffices to establish `hm : _ from ⟨𝒰.glueMorphisms m hm, 𝒰.ι_glueMorphisms m hm false, 𝒰.ι_glueMorphisms m hm true⟩`. Introduce and unpack `(_ | _) (_ | _)`.

Express the relevant statement in the definitionally equal form `pullback.fst u u ≫ a = pullback.snd u u ≫ a`. Rewrite using `[fst_eq_snd_of_mono_eq]`. Express the relevant statement in the definitionally equal form `pullback.fst u v ≫ a = pullback.snd u v ≫ b`. Rewrite using `[← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]`. Express the relevant statement in the definitionally equal form `pullback.fst v u ≫ b = pullback.snd v u ≫ a`.

Rewrite using `[← h.flip.isoPullback_inv_fst, ← h.flip.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]`. Express the relevant statement in the definitionally equal form `pullback.fst v v ≫ b = pullback.snd v v ≫ b`. Rewrite using `[fst_eq_snd_of_mono_eq]`.
-/
theorem exists_glue {X U V W Y : Scheme.{0}} {u : U ⟶ X} {v : V ⟶ X} {p : W ⟶ U} {q : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v] (h : IsPullback p q u v)
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (a : U ⟶ Y) (b : V ⟶ Y) (hab : p ≫ a = q ≫ b) :
    ∃ φ : X ⟶ Y, u ≫ φ = a ∧ v ≫ φ = b := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  let m : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) a b i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  suffices hm : _ from ⟨𝒰.glueMorphisms m hm, 𝒰.ι_glueMorphisms m hm false, 𝒰.ι_glueMorphisms m hm true⟩
  · rintro (_ | _) (_ | _)
    · change pullback.fst u u ≫ a = pullback.snd u u ≫ a
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst u v ≫ a = pullback.snd u v ≫ b
      rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v u ≫ b = pullback.snd v u ≫ a
      rw [← h.flip.isoPullback_inv_fst, ← h.flip.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v v ≫ b = pullback.snd v v ≫ b
      rw [fst_eq_snd_of_mono_eq]

/- English proof (translation)
Set `T : Bool → Scheme.{0}` to `fun i => Bool.rec U V i`. Set `t : ∀ i, T i ⟶ X` to `fun i => Bool.rec u v i`. Apply the tactic sequence `have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption`. Set `𝒰 : X.OpenCover` to `Scheme.Cover.mkOfCovers Bool T t (fun x => by`. Break down `hc x with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases.

Conclude with `⟨false, y, hy⟩`. Conclude with `⟨true, y, hy⟩)`. Use `Scheme.isPullback_of_openCover _ _ _ _ 𝒰 ?_` and prove the remaining obligations. Introduce and unpack `(_ | _)`. Express the relevant statement in the definitionally equal form `IsPullback (pullback.snd a u) (pullback.fst a u ≫ b) (u ≫ f) g`.

Apply the tactic sequence `refine hU'.of_iso hU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp`. Express the relevant statement in the definitionally equal form `IsPullback (pullback.snd a v) (pullback.fst a v ≫ b) (v ≫ f) g`. Apply the tactic sequence `refine hV'.of_iso hV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp`.
-/
theorem isPullback_of_two {W X Y Z U V U' V' : Scheme.{0}} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    {u' : U' ⟶ W} {v' : V' ⟶ W} {aU : U' ⟶ U} {aV : V' ⟶ V}
    (hU : IsPullback aU u' u a) (hV : IsPullback aV v' v a)
    (hU' : IsPullback aU (u' ≫ b) (u ≫ f) g) (hV' : IsPullback aV (v' ≫ b) (v ≫ f) g) :
    IsPullback a b f g := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 ?_
  rintro (_ | _)
  · change IsPullback (pullback.snd a u) (pullback.fst a u ≫ b) (u ≫ f) g
    refine hU'.of_iso hU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · change IsPullback (pullback.snd a v) (pullback.fst a v ≫ b) (v ≫ f) g
    refine hV'.of_iso hV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

/- English proof (translation)
The claim follows from `inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))`.
-/
theorem isOpenImmersion_inl {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inl p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))

/- English proof (translation)
The claim follows from `inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.right))`.
-/
theorem isOpenImmersion_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inr p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.right))

/- English proof (translation)
Take `⟨i, x, hx⟩` from `Scheme.IsLocallyDirected.ι_jointly_surjective (span p q) z`. Break down `i with _ | _ | _` into its components or cases. Use `Or.inl ⟨p x, Eq.trans ?_ hx⟩` and prove the remaining obligations. Conclude with `congrArg (fun g => g x) (colimit.w (span p q) WalkingSpan.Hom.fst)`. Conclude with `Or.inl ⟨x, hx⟩`.

Conclude with `Or.inr ⟨x, hx⟩`.
-/
theorem pushout_cover {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] (z : (pushout p q : Scheme.{0})) :
    z ∈ Set.range (pushout.inl p q) ∨ z ∈ Set.range (pushout.inr p q) := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span p q) z
  rcases i with _ | _ | _
  · refine Or.inl ⟨p x, Eq.trans ?_ hx⟩
    exact congrArg (fun g => g x) (colimit.w (span p q) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩

/- English proof (translation)
Take `⟨k, fi, fj, w, h1, h2⟩` from `(Scheme.IsLocallyDirected.ι_eq_ι_iff (span p q) (i := WalkingSpan.left) (j := WalkingSpan.right)).1 h`. Break down `fi with _ | _` into its components or cases. Break down `fj with _ | _` into its components or cases. Break down `fj with _ | _` into its components or cases. Conclude with `⟨w, h1, h2⟩`.
-/
theorem exists_of_inl_eq_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] {x : U} {y : V} (h : pushout.inl p q x = pushout.inr p q y) :
    ∃ w : W, p w = x ∧ q w = y := by
  obtain ⟨k, fi, fj, w, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span p q)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).1 h
  rcases fi with _ | _
  · rcases fj with _ | _
  · rcases fj with _ | _
    exact ⟨w, h1, h2⟩

/- English proof (translation)
Establish `H : IsPullback φW p.left p₀.left φU`. Use `IsPullback.of_bot ?_ hp hU` and prove the remaining obligations. Rewrite using `[Over.w p, Over.w p₀]` and apply the resulting hypothesis. Use `⟨H, ?_⟩` and prove the remaining obligations. Establish `hβ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap β)`.

Use `⟨⟨⟨fun x => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩, ?_⟩, inferInstanceAs (QuasiCompact (spMap β))⟩` and prove the remaining obligations. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Use `algebraize [β]`. Conclude with `RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat k K))`. Conclude with `MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip (MorphismProperty.of_isPullback hU.flip hβ) ‹_›`.
-/
theorem model_open {k K : Type} [Field k] [Field K] (β : k →+* K) {U W : Over (Sp K)} (p : W ⟶ U)
    [IsOpenImmersion p.left] {U₀ W₀ : Over (Sp k)} {φU : U.left ⟶ U₀.left} {φW : W.left ⟶ W₀.left}
    (hU : IsPullback φU U.hom U₀.hom (spMap β)) (hW : IsPullback φW W.hom W₀.hom (spMap β))
    (p₀ : W₀ ⟶ U₀) (hp : φW ≫ p₀.left = p.left ≫ φU) :
    IsPullback φW p.left p₀.left φU ∧ IsOpenImmersion p₀.left := by
  have H : IsPullback φW p.left p₀.left φU := by
    refine IsPullback.of_bot ?_ hp hU
    rwa [Over.w p, Over.w p₀]
  refine ⟨H, ?_⟩
  have hβ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap β) := by
    refine ⟨⟨⟨fun x => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩, ?_⟩,
      inferInstanceAs (QuasiCompact (spMap β))⟩
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [β]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat k K))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip (MorphismProperty.of_isPullback hU.flip hβ) ‹_›

/- English proof (translation)
Introduce `k K _ _ β X U V W u v p q hu hv h hc U₀ V₀ W₀ φU φV φW hU hV hW p₀ q₀ hp hq`. Establish `: IsOpenImmersion p.left` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip hv`. Establish `: IsOpenImmersion q.left` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) h hu`. Take `⟨Hp, _⟩` from `model_open β p hU hW p₀ hp`. Take `⟨Hq, _⟩` from `model_open β q hV hW q₀ hq`.

Use `isOpenImmersion_inl p₀.left q₀.left` as an intermediate fact. Use `isOpenImmersion_inr p₀.left q₀.left` as an intermediate fact. Take `⟨φ, h1, h2⟩` from `exists_glue h hc (φU ≫ pushout.inl p₀.left q₀.left) (φV ≫ pushout.inr p₀.left q₀.left) (by`. Rewrite using `[← Category.assoc, ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, pushout.condition])`. Establish `e1 (x : U.left) : φ (u.left x) = pushout.inl p₀.left q₀.left (φU x)` using `congrArg (fun g => g x) h1`.

Establish `e2 (x : V.left) : φ (v.left x) = pushout.inr p₀.left q₀.left (φV x)` using `congrArg (fun g => g x) h2`. Establish `e3 (w : W.left) : u.left (p.left w) = v.left (q.left w)` using `congrArg (fun g => g w) h.w`. Use `⟨Over.mk (pushout.desc U₀.hom V₀.hom ((Over.w p₀).trans (Over.w q₀).symm)), φ, ?_⟩` and prove the remaining obligations. Use `isPullback_of_two (pushout_cover p₀.left q₀.left) (u' := u.left) (v' := v.left) (aU := φU) (aV := φV) ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `IsOpenImmersion.isPullback _ _ _ _ h1 ?_` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Break down `hc x with hx | ⟨x, rfl⟩` into its components or cases. Conclude with `hx`.

Take `⟨w, -, hw⟩` from `exists_of_inl_eq_inr _ _ (hy.trans (e2 x))`. Take `⟨z, -, rfl⟩` from `Scheme.exists_preimage_of_isPullback Hq w x hw`. Conclude with `⟨p.left z, e3 z⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨φU y, (e1 y).symm⟩`.

Use `IsOpenImmersion.isPullback _ _ _ _ h2 ?_` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Break down `hc x with ⟨x, rfl⟩ | hx` into its components or cases.

Take `⟨w, hw, -⟩` from `exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm`. Take `⟨z, -, rfl⟩` from `Scheme.exists_preimage_of_isPullback Hp w x hw`. Conclude with `⟨q.left z, (e3 z).symm⟩`. Conclude with `hx`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨φV y, (e2 y).symm⟩`. Simplify `hU` using `only [Over.w u, Over.mk_hom, pushout.inl_desc]`. Simplify `hV` using `only [Over.w v, Over.mk_hom, pushout.inr_desc]`.
-/
theorem glue_models : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (X U V W : Over (Sp K)) (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V), IsOpenImmersion u.left → IsOpenImmersion v.left → IsPullback p.left q.left u.left v.left → (∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left) → ∀ (U₀ V₀ W₀ : Over (Sp k)) (φU : U.left ⟶ U₀.left) (φV : V.left ⟶ V₀.left) (φW : W.left ⟶ W₀.left), IsPullback φU U.hom U₀.hom (spMap β) → IsPullback φV V.hom V₀.hom (spMap β) → IsPullback φW W.hom W₀.hom (spMap β) → ∀ (p₀ : W₀ ⟶ U₀) (q₀ : W₀ ⟶ V₀), φW ≫ p₀.left = p.left ≫ φU → φW ≫ q₀.left = q.left ≫ φV → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro k K _ _ β X U V W u v p q hu hv h hc U₀ V₀ W₀ φU φV φW hU hV hW p₀ q₀ hp hq
  have : IsOpenImmersion p.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip hv
  have : IsOpenImmersion q.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h hu
  obtain ⟨Hp, _⟩ := model_open β p hU hW p₀ hp
  obtain ⟨Hq, _⟩ := model_open β q hV hW q₀ hq
  have := isOpenImmersion_inl p₀.left q₀.left
  have := isOpenImmersion_inr p₀.left q₀.left
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (φU ≫ pushout.inl p₀.left q₀.left) (φV ≫ pushout.inr p₀.left q₀.left) (by
    rw [← Category.assoc, ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, pushout.condition])
  have e1 (x : U.left) : φ (u.left x) = pushout.inl p₀.left q₀.left (φU x) := congrArg (fun g => g x) h1
  have e2 (x : V.left) : φ (v.left x) = pushout.inr p₀.left q₀.left (φV x) := congrArg (fun g => g x) h2
  have e3 (w : W.left) : u.left (p.left w) = v.left (q.left w) := congrArg (fun g => g w) h.w
  refine ⟨Over.mk (pushout.desc U₀.hom V₀.hom ((Over.w p₀).trans (Over.w q₀).symm)), φ, ?_⟩
  refine isPullback_of_two (pushout_cover p₀.left q₀.left) (u' := u.left) (v' := v.left) (aU := φU) (aV := φV)
    ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨p.left z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨q.left z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨φV y, (e2 y).symm⟩
  · simpa only [Over.w u, Over.mk_hom, pushout.inl_desc] using hU
  · simpa only [Over.w v, Over.mk_hom, pushout.inr_desc] using hV

end GlobalTheory.GlueModels
