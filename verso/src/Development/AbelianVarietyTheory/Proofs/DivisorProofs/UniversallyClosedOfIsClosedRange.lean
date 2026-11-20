import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperLimit

def GoodAt {Y P : Scheme.{0}} (q : Y ⟶ P) (y : Y) : Prop :=
  ∃ W : P.Opens, q y ∈ W ∧ UniversallyClosed (q ∣_ W)

/- English proof (translation)
Establish `H : IsPullback (h.lift v' (r' ≫ m) (by rw [Category.assoc, h'.w])) r' r m` using `IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ _) h`. Conclude with `MorphismProperty.of_isPullback H ‹_›`.
-/
theorem universallyClosed_of_factor {Y P V U V' U' : Scheme.{0}} {q : Y ⟶ P} {v : V ⟶ Y} {r : V ⟶ U}
    {j : U ⟶ P} (h : IsPullback v r q j) [UniversallyClosed r] {v' : V' ⟶ Y} {r' : V' ⟶ U'} (m : U' ⟶ U)
    (h' : IsPullback v' r' q (m ≫ j)) : UniversallyClosed r' := by
  have H : IsPullback (h.lift v' (r' ≫ m) (by rw [Category.assoc, h'.w])) r' r m :=
    IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback H ‹_›

/- English proof (translation)
Take `⟨W, hW, _⟩` from `H`. Use `⟨g ⁻¹ᵁ W, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (q' y) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]` and apply the resulting hypothesis. Use `universallyClosed_of_factor (isPullback_morphismRestrict q W).flip (g ∣_ W) (v' := (q' ⁻¹ᵁ g ⁻¹ᵁ W).ι ≫ a) ?_` and prove the remaining obligations.

Rewrite using `[morphismRestrict_ι]`. Conclude with `(isPullback_morphismRestrict q' (g ⁻¹ᵁ W)).flip.paste_horiz h`.
-/
theorem GoodAt.baseChange {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    (h : IsPullback a q' q g) {y : Y'} (H : GoodAt q (a y)) : GoodAt q' y := by
  obtain ⟨W, hW, _⟩ := H
  refine ⟨g ⁻¹ᵁ W, ?_, ?_⟩
  · change g (q' y) ∈ W
    rwa [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]
  · refine universallyClosed_of_factor (isPullback_morphismRestrict q W).flip (g ∣_ W)
      (v' := (q' ⁻¹ᵁ g ⁻¹ᵁ W).ι ≫ a) ?_
    rw [morphismRestrict_ι]
    exact (isPullback_morphismRestrict q' (g ⁻¹ᵁ W)).flip.paste_horiz h

/- English proof (translation)
Take `⟨W, hW, _⟩` from `H`. Use `⟨g ⁻¹ᵁ W, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (q' y) ∈ W`. Rewrite using `[← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]` and apply the resulting hypothesis. Establish `h₁ : UniversallyClosed ((a ≫ q) ∣_ W)`.

Rewrite using `[morphismRestrict_comp]`. Use `infer_instance`. Rewrite `h₁` using `[h, morphismRestrict_comp]`. Conclude with `UniversallyClosed.of_comp_of_isSeparated _ (g ∣_ W)`.
-/
theorem GoodAt.of_comp {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    [UniversallyClosed a] [IsSeparated g] (h : a ≫ q = q' ≫ g) {y : Y'} (H : GoodAt q (a y)) : GoodAt q' y := by
  obtain ⟨W, hW, _⟩ := H
  refine ⟨g ⁻¹ᵁ W, ?_, ?_⟩
  · change g (q' y) ∈ W
    rwa [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  · have h₁ : UniversallyClosed ((a ≫ q) ∣_ W) := by
      rw [morphismRestrict_comp]
      infer_instance
    rw [h, morphismRestrict_comp] at h₁
    exact UniversallyClosed.of_comp_of_isSeparated _ (g ∣_ W)

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨a y, by rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `⟨y, hy⟩`.

Take `⟨w, -, hw⟩` from `Scheme.exists_preimage_of_isPullback h y z hy`. Conclude with `⟨w, hw⟩`.
-/
theorem range_eq_of_isPullback {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    (h : IsPullback a q' q g) : Set.range q' = g ⁻¹' Set.range q := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨a y, by rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback h y z hy
    exact ⟨w, hw⟩

/- English proof (translation)
Use `((isLocallyClosed_tfae (Set.range q)).out 0 2).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨W, hW, _⟩` from `H y`. Use `⟨W, W.2.mem_nhds hW, ?_⟩` and prove the remaining obligations. Use `(q ∣_ W).isClosedMap.isClosed_range` as an intermediate fact.

Rewrite `this` using `[range_eq_of_isPullback (isPullback_morphismRestrict q W).flip]`. Conclude with `this`.
-/
theorem isLocallyClosed_range {Y P : Scheme.{0}} {q : Y ⟶ P} (H : ∀ y, GoodAt q y) :
    IsLocallyClosed (Set.range q) := by
  refine ((isLocallyClosed_tfae (Set.range q)).out 0 2).2 ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨W, hW, _⟩ := H y
  refine ⟨W, W.2.mem_nhds hW, ?_⟩
  have := (q ∣_ W).isClosedMap.isClosed_range
  rw [range_eq_of_isPullback (isPullback_morphismRestrict q W).flip] at this
  exact this

/- English proof (translation)
Use `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @UniversallyClosed) fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ Set.range q`. Take `⟨y, rfl⟩` from `hz`. Conclude with `H y`. Set `W : P.Opens` to `⟨(Set.range q)ᶜ, h.isOpen_compl⟩`.

Use `⟨W, hz, ?_⟩` and prove the remaining obligations. Establish `: IsEmpty (q ⁻¹ᵁ W : Y.Opens)` using `⟨fun y => y.2 ⟨y.1, rfl⟩⟩`. Use `infer_instance`.
-/
theorem universallyClosed_of_isClosed_range {Y P : Scheme.{0}} {q : Y ⟶ P} (H : ∀ y, GoodAt q y)
    (h : IsClosed (Set.range q)) : UniversallyClosed q := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @UniversallyClosed) fun z => ?_
  by_cases hz : z ∈ Set.range q
  · obtain ⟨y, rfl⟩ := hz
    exact H y
  · let W : P.Opens := ⟨(Set.range q)ᶜ, h.isOpen_compl⟩
    refine ⟨W, hz, ?_⟩
    have : IsEmpty (q ⁻¹ᵁ W : Y.Opens) := ⟨fun y => y.2 ⟨y.1, rfl⟩⟩
    infer_instance

/- English proof (translation)
Establish `hq` using `IsPullback.of_hasPullback q (pullback.fst t g)`. Set `π' : pullback q (pullback.fst t g) ⟶ pullback p g` to `pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _ ≫ pullback.snd _ _) (by`. Rewrite using `[Category.assoc, w, hq.w_assoc, pullback.condition, Category.assoc])`. Establish `e : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `hπ : IsPullback (pullback.fst _ _) π' π (pullback.fst p g)`.

Use `IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback p g)` and prove the remaining obligations. Rewrite using `[e, w]`. Conclude with `hq.paste_vert (.of_hasPullback t g)`. Establish `: UniversallyClosed π'` using `MorphismProperty.of_isPullback hπ ‹_›`. Establish `: Surjective π'` using `MorphismProperty.of_isPullback hπ ‹_›`.

Rewrite using `[← range_eq_of_isPullback hq]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Establish `: UniversallyClosed (pullback.snd q (pullback.fst t g) ≫ pullback.snd t g)`. Rewrite using `[← e]`.

Use `infer_instance`. Use `UniversallyClosed.of_comp_of_isSeparated (pullback.snd q (pullback.fst t g)) (pullback.snd t g)` as an intermediate fact. Conclude with `(pullback.snd q (pullback.fst t g)).isClosedMap.isClosed_range`. Introduce `h`. Use `universallyClosed_of_isClosed_range (fun y => (H _).baseChange hq (y := y)) h` as an intermediate fact.

Establish `: UniversallyClosed (π' ≫ pullback.snd p g)`. Rewrite using `[e]`. Use `infer_instance`. Conclude with `UniversallyClosed.of_comp_surjective π' _`.
-/
theorem universallyClosed_snd_iff {X Y P S T : Scheme.{0}} {p : X ⟶ S} {π : Y ⟶ X} {q : Y ⟶ P} {t : P ⟶ S}
    [UniversallyClosed π] [Surjective π] [IsProper t] (w : π ≫ p = q ≫ t) (H : ∀ y, GoodAt q y) (g : T ⟶ S) :
    UniversallyClosed (pullback.snd p g) ↔ IsClosed (pullback.fst t g ⁻¹' Set.range q) := by
  have hq := IsPullback.of_hasPullback q (pullback.fst t g)
  let π' : pullback q (pullback.fst t g) ⟶ pullback p g :=
    pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, w, hq.w_assoc, pullback.condition, Category.assoc])
  have e : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have hπ : IsPullback (pullback.fst _ _) π' π (pullback.fst p g) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback p g)
    rw [e, w]
    exact hq.paste_vert (.of_hasPullback t g)
  have : UniversallyClosed π' := MorphismProperty.of_isPullback hπ ‹_›
  have : Surjective π' := MorphismProperty.of_isPullback hπ ‹_›
  rw [← range_eq_of_isPullback hq]
  constructor
  · intro _
    have : UniversallyClosed (pullback.snd q (pullback.fst t g) ≫ pullback.snd t g) := by
      rw [← e]
      infer_instance
    have := UniversallyClosed.of_comp_of_isSeparated (pullback.snd q (pullback.fst t g)) (pullback.snd t g)
    exact (pullback.snd q (pullback.fst t g)).isClosedMap.isClosed_range
  · intro h
    have := universallyClosed_of_isClosed_range (fun y => (H _).baseChange hq (y := y)) h
    have : UniversallyClosed (π' ≫ pullback.snd p g) := by
      rw [e]
      infer_instance
    exact UniversallyClosed.of_comp_surjective π' _

def HasCover {X S : Scheme.{0}} (p : X ⟶ S) (V : Set X) : Prop :=
  ∃ (Y P : Scheme.{0}) (π : Y ⟶ X) (q : Y ⟶ P) (t : P ⟶ S), UniversallyClosed π ∧ Surjective π ∧ IsProper t ∧
    π ≫ p = q ≫ t ∧ ∀ y, π y ∈ V → GoodAt q y

/- English proof (translation)
Take `⟨Y, P, π, q, t, _, _, _, w, H⟩` from `h`. Take `⟨Y', P', π', q', t', _, _, _, w', H'⟩` from `h'`. Set `Q : pullback π π' ⟶ pullback t t'` to `pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ q') (by`. Rewrite using `[Category.assoc, Category.assoc, ← w, ← w', pullback.condition_assoc])`. Establish `e₁ : Q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q` using `pullback.lift_fst _ _ _`.

Establish `e₂ : Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q'` using `pullback.lift_snd _ _ _`. Use `⟨_, _, pullback.fst π π' ≫ π, Q, pullback.fst t t' ≫ t, inferInstance, inferInstance, inferInstance, by rw [reassoc_of% e₁, Category.assoc, w], ?_⟩` and prove the remaining obligations. Introduce and unpack `y (hy | hy)`. Conclude with `GoodAt.of_comp e₁.symm (H _ hy)`. Rewrite `hy` using `[pullback.condition]`.

Conclude with `GoodAt.of_comp e₂.symm (H' _ hy)`.
-/
theorem HasCover.union {X S : Scheme.{0}} {p : X ⟶ S} {V V' : Set X} (h : HasCover p V) (h' : HasCover p V') :
    HasCover p (V ∪ V') := by
  obtain ⟨Y, P, π, q, t, _, _, _, w, H⟩ := h
  obtain ⟨Y', P', π', q', t', _, _, _, w', H'⟩ := h'
  let Q : pullback π π' ⟶ pullback t t' :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ q') (by
      rw [Category.assoc, Category.assoc, ← w, ← w', pullback.condition_assoc])
  have e₁ : Q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
  have e₂ : Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q' := pullback.lift_snd _ _ _
  refine ⟨_, _, pullback.fst π π' ≫ π, Q, pullback.fst t t' ≫ t, inferInstance, inferInstance, inferInstance,
    by rw [reassoc_of% e₁, Category.assoc, w], ?_⟩
  rintro y (hy | hy)
  · exact GoodAt.of_comp e₁.symm (H _ hy)
  · rw [pullback.condition] at hy
    exact GoodAt.of_comp e₂.symm (H' _ hy)

/- English proof (translation)
Establish `: IsSeparated a` using `MorphismProperty.of_isPullback h.flip ‹_›`. Set `γ : U ⟶ pullback a i` to `pullback.lift δ (𝟙 _) (by simpa)`. Establish `e : γ ≫ pullback.snd a i = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `e' : γ ≫ pullback.fst a i = δ` using `pullback.lift_fst _ _ _`. Establish `: IsClosedImmersion (γ ≫ pullback.snd a i)` using `by rw [e]; infer_instance`.

Establish `: IsClosedImmersion γ` using `IsClosedImmersion.of_comp γ (pullback.snd a i)`. Establish `ho` using `(pullback.fst a i).isOpenEmbedding.isOpenMap _ γ.isClosedEmbedding.isClosed_range.isOpen_compl`. Use `ho using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Scheme.Pullback.range_fst, Set.compl_eq_univ_diff, Set.image_diff (pullback.fst a i).isOpenEmbedding.injective, Set.image_univ, ← Set.range_comp, ← e']`. Both sides reduce to the same expression.
-/
theorem isOpen_diff_range {X U P S Z : Scheme.{0}} {p : X ⟶ S} {t : P ⟶ S} [IsSeparated t] {a : Z ⟶ X} {b : Z ⟶ P}
    (h : IsPullback a b p t) (i : U ⟶ X) [IsOpenImmersion i] (δ : U ⟶ Z) (hδ : δ ≫ a = i) :
    IsOpen (a ⁻¹' Set.range i \ Set.range δ) := by
  have : IsSeparated a := MorphismProperty.of_isPullback h.flip ‹_›
  let γ : U ⟶ pullback a i := pullback.lift δ (𝟙 _) (by simpa)
  have e : γ ≫ pullback.snd a i = 𝟙 _ := pullback.lift_snd _ _ _
  have e' : γ ≫ pullback.fst a i = δ := pullback.lift_fst _ _ _
  have : IsClosedImmersion (γ ≫ pullback.snd a i) := by rw [e]; infer_instance
  have : IsClosedImmersion γ := IsClosedImmersion.of_comp γ (pullback.snd a i)
  have ho := (pullback.fst a i).isOpenEmbedding.isOpenMap _ γ.isClosedEmbedding.isClosed_range.isOpen_compl
  convert ho using 1
  rw [← Scheme.Pullback.range_fst, Set.compl_eq_univ_diff,
    Set.image_diff (pullback.fst a i).isOpenEmbedding.injective, Set.image_univ, ← Set.range_comp, ← e']
  rfl

/- English proof (translation)
Set `a` to `pullback.fst p t`. Set `b` to `pullback.snd p t`. Set `δ : U ⟶ pullback p t` to `pullback.lift i j w`. Establish `e₁ : δ ≫ a = i` using `pullback.lift_fst _ _ _`. Establish `e₂ : δ ≫ b = j` using `pullback.lift_snd _ _ _`.

Establish `e₁' (u : U) : a (δ u) = i u` using `by rw [← Scheme.Hom.comp_apply, e₁]`. Establish `e₂' (u : U) : b (δ u) = j u` using `by rw [← Scheme.Hom.comp_apply, e₂]`. Establish `o₁` using `isOpen_diff_range (.of_hasPullback p t) i δ e₁`. Establish `o₂` using `isOpen_diff_range (IsPullback.of_hasPullback p t).flip j δ e₂`. Set `Γ : TopologicalSpace.Closeds ↥(pullback p t)` to `⟨_, (o₁.union o₂).isClosed_compl⟩`.

Set `I` to `Scheme.IdealSheafData.vanishingIdeal Γ`. Establish `hI : Set.range I.subschemeι = Γ`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Establish `mem (z : ↥(pullback p t)) : z ∈ Set.range I.subschemeι ↔ (a z ∈ Set.range i → z ∈ Set.range δ) ∧ (b z ∈ Set.range j → z ∈ Set.range δ)`. Rewrite using `[hI]`.

Express the relevant statement in the definitionally equal form `¬ ((a z ∈ Set.range i ∧ z ∉ Set.range δ) ∨ (b z ∈ Set.range j ∧ z ∉ Set.range δ)) ↔ _`. The claim follows by propositional logic. Use `⟨_, _, I.subschemeι ≫ a, I.subschemeι ≫ b, t, inferInstance, ⟨fun x => ?_⟩, ‹_›, by rw [Category.assoc, Category.assoc, pullback.condition], fun y hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ Set.range i`. Take `⟨u, rfl⟩` from `hx`.

Take `⟨y, hy⟩` from `(mem (δ u)).2 ⟨fun _ => ⟨u, rfl⟩, fun _ => ⟨u, rfl⟩⟩`. Conclude with `⟨y, by rw [Scheme.Hom.comp_apply, hy, e₁']⟩`. Set `s : X ⟶ pullback p t` to `pullback.lift (𝟙 _) (p ≫ σ) (by simp [hσ])`. Establish `f₁ : a (s x) = x`. Rewrite using `[← Scheme.Hom.comp_apply, show s ≫ a = 𝟙 _ from pullback.lift_fst _ _ _]`.

Both sides reduce to the same expression. Establish `f₂ : b (s x) = σ (p x)`. Rewrite using `[← Scheme.Hom.comp_apply, show s ≫ b = p ≫ σ from pullback.lift_snd _ _ _, Scheme.Hom.comp_apply]`. Take `⟨y, hy⟩` from `(mem (s x)).2 ⟨fun h => (hx (f₁ ▸ h)).elim, fun h => (hd _ (f₂ ▸ h)).elim⟩`. Conclude with `⟨y, by rw [Scheme.Hom.comp_apply, hy, f₁]⟩`.

Take `⟨u, hu⟩` from `((mem _).1 ⟨y, rfl⟩).1 hy`. Use `⟨j.opensRange, ⟨u, by rw [Scheme.Hom.comp_apply, ← hu, e₂']⟩, ?_⟩` and prove the remaining obligations. Set `c : pullback I.subschemeι δ ⟶ pullback (I.subschemeι ≫ b) j` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc, e₂])`. Establish `g₁ : c ≫ pullback.fst _ _ = pullback.fst _ _` using `pullback.lift_fst _ _ _`. Establish `g₂ : c ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`.

Establish `: Surjective c` using `⟨fun z => by`. Take `⟨u, hu⟩` from `((mem _).1 ⟨pullback.fst (I.subschemeι ≫ b) j z, rfl⟩).2 ⟨pullback.snd (I.subschemeι ≫ b) j z, by`. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩`. Take `⟨v, hv, -⟩` from `Scheme.exists_preimage_of_isPullback (.of_hasPullback I.subschemeι δ) _ _ hu.symm`. Use `⟨v, (pullback.fst (I.subschemeι ≫ b) j).isOpenEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, g₁, hv]⟩`. Establish `: UniversallyClosed (c ≫ pullback.snd (I.subschemeι ≫ b) j)`. Rewrite using `[g₂]`. Use `infer_instance`. Use `UniversallyClosed.of_comp_surjective c (pullback.snd (I.subschemeι ≫ b) j)` as an intermediate fact.

Use `universallyClosed_of_factor (.of_hasPullback (I.subschemeι ≫ b) j) j.isoOpensRange.inv (v' := ((I.subschemeι ≫ b) ⁻¹ᵁ j.opensRange).ι) ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.isoOpensRange_inv_comp]`. Conclude with `(isPullback_morphismRestrict _ _).flip`.
-/
theorem hasCover_of_section {X U P S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (i : U ⟶ X) [IsOpenImmersion i]
    (t : P ⟶ S) [IsProper t] (j : U ⟶ P) [IsOpenImmersion j] (w : i ≫ p = j ≫ t) (σ : S ⟶ P) (hσ : σ ≫ t = 𝟙 _)
    (hd : ∀ s, σ s ∉ Set.range j) : HasCover p (Set.range i) := by
  let a := pullback.fst p t
  let b := pullback.snd p t
  let δ : U ⟶ pullback p t := pullback.lift i j w
  have e₁ : δ ≫ a = i := pullback.lift_fst _ _ _
  have e₂ : δ ≫ b = j := pullback.lift_snd _ _ _
  have e₁' (u : U) : a (δ u) = i u := by rw [← Scheme.Hom.comp_apply, e₁]
  have e₂' (u : U) : b (δ u) = j u := by rw [← Scheme.Hom.comp_apply, e₂]
  have o₁ := isOpen_diff_range (.of_hasPullback p t) i δ e₁
  have o₂ := isOpen_diff_range (IsPullback.of_hasPullback p t).flip j δ e₂
  let Γ : TopologicalSpace.Closeds ↥(pullback p t) := ⟨_, (o₁.union o₂).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Γ
  have hI : Set.range I.subschemeι = Γ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have mem (z : ↥(pullback p t)) : z ∈ Set.range I.subschemeι ↔
      (a z ∈ Set.range i → z ∈ Set.range δ) ∧ (b z ∈ Set.range j → z ∈ Set.range δ) := by
    rw [hI]
    change ¬ ((a z ∈ Set.range i ∧ z ∉ Set.range δ) ∨ (b z ∈ Set.range j ∧ z ∉ Set.range δ)) ↔ _
    tauto
  refine ⟨_, _, I.subschemeι ≫ a, I.subschemeι ≫ b, t, inferInstance, ⟨fun x => ?_⟩, ‹_›,
    by rw [Category.assoc, Category.assoc, pullback.condition], fun y hy => ?_⟩
  · by_cases hx : x ∈ Set.range i
    · obtain ⟨u, rfl⟩ := hx
      obtain ⟨y, hy⟩ := (mem (δ u)).2 ⟨fun _ => ⟨u, rfl⟩, fun _ => ⟨u, rfl⟩⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, e₁']⟩
    · let s : X ⟶ pullback p t := pullback.lift (𝟙 _) (p ≫ σ) (by simp [hσ])
      have f₁ : a (s x) = x := by
        rw [← Scheme.Hom.comp_apply, show s ≫ a = 𝟙 _ from pullback.lift_fst _ _ _]
        rfl
      have f₂ : b (s x) = σ (p x) := by
        rw [← Scheme.Hom.comp_apply, show s ≫ b = p ≫ σ from pullback.lift_snd _ _ _, Scheme.Hom.comp_apply]
      obtain ⟨y, hy⟩ := (mem (s x)).2 ⟨fun h => (hx (f₁ ▸ h)).elim, fun h => (hd _ (f₂ ▸ h)).elim⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, f₁]⟩
  · obtain ⟨u, hu⟩ := ((mem _).1 ⟨y, rfl⟩).1 hy
    refine ⟨j.opensRange, ⟨u, by rw [Scheme.Hom.comp_apply, ← hu, e₂']⟩, ?_⟩
    let c : pullback I.subschemeι δ ⟶ pullback (I.subschemeι ≫ b) j :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc, e₂])
    have g₁ : c ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
    have g₂ : c ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have : Surjective c := ⟨fun z => by
      obtain ⟨u, hu⟩ := ((mem _).1 ⟨pullback.fst (I.subschemeι ≫ b) j z, rfl⟩).2
        ⟨pullback.snd (I.subschemeι ≫ b) j z, by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩
      obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback I.subschemeι δ) _ _ hu.symm
      refine ⟨v, (pullback.fst (I.subschemeι ≫ b) j).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, g₁, hv]⟩
    have : UniversallyClosed (c ≫ pullback.snd (I.subschemeι ≫ b) j) := by
      rw [g₂]
      infer_instance
    have := UniversallyClosed.of_comp_surjective c (pullback.snd (I.subschemeι ≫ b) j)
    refine universallyClosed_of_factor (.of_hasPullback (I.subschemeι ≫ b) j) j.isoOpensRange.inv
      (v' := ((I.subschemeι ≫ b) ⁻¹ᵁ j.opensRange).ι) ?_
    rw [Scheme.Hom.isoOpensRange_inv_comp]
    exact (isPullback_morphismRestrict _ _).flip

/- English proof (translation)
Establish `: LocallyOfFiniteType (coprod.desc (i ≫ p) (𝟙 (Sp R)))`. Use `IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (coprodOpenCover.{0, 0} U (Sp R)) ?_` and prove the remaining obligations. Introduce and unpack `⟨_ | _⟩`. Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (coprod.inl ≫ _)`. Rewrite using `[coprod.inl_desc]`.

Use `infer_instance`. Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (coprod.inr ≫ _)`. Rewrite using `[coprod.inr_desc]`. Conclude with `MorphismProperty.id_mem (W := @LocallyOfFiniteType) _`. Take `⟨P, t, j, _, _, e⟩` from `ArcProper.exists_isOpenImmersion_isProper (coprod.desc (i ≫ p) (𝟙 (Sp R)))`.

Use `hasCover_of_section p i t (coprod.inl ≫ j) (by simp [e]) (coprod.inr ≫ j) (by simp [e]) ?_` and prove the remaining obligations. Introduce and unpack `s ⟨u, hu⟩`. Conclude with `inl_ne_inr U (Sp R) u s (j.isOpenEmbedding.injective hu)`.
-/
theorem hasCover_affine {R : Type} [CommRing R] {X U : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p]
    [LocallyOfFiniteType p] (i : U ⟶ X) [IsOpenImmersion i] [IsAffine U] : HasCover p (Set.range i) := by
  have : LocallyOfFiniteType (coprod.desc (i ≫ p) (𝟙 (Sp R))) := by
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (coprodOpenCover.{0, 0} U (Sp R)) ?_
    rintro ⟨_ | _⟩
    · change LocallyOfFiniteType (coprod.inl ≫ _)
      rw [coprod.inl_desc]
      infer_instance
    · change LocallyOfFiniteType (coprod.inr ≫ _)
      rw [coprod.inr_desc]
      exact MorphismProperty.id_mem (W := @LocallyOfFiniteType) _
  obtain ⟨P, t, j, _, _, e⟩ := ArcProper.exists_isOpenImmersion_isProper (coprod.desc (i ≫ p) (𝟙 (Sp R)))
  refine hasCover_of_section p i t (coprod.inl ≫ j) (by simp [e]) (coprod.inr ≫ j) (by simp [e]) ?_
  rintro s ⟨u, hu⟩
  exact inl_ne_inr U (Sp R) u s (j.isOpenEmbedding.injective hu)

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Use `compact_open_induction_on (P := fun S : X.Opens => HasCover p S) ⊤ isCompact_univ ?_ ?_` and prove the remaining obligations. Conclude with `⟨X, _, 𝟙 _, p, 𝟙 _, inferInstance, inferInstance, inferInstance, by simp, fun _ h => h.elim⟩`. Introduce `S _ W h`. Establish `: IsAffine W.1` using `W.2`.

Use `h.union (hasCover_affine p W.1.ι)` as an intermediate fact. Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis.
-/
theorem hasCover_univ {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] : HasCover p Set.univ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine compact_open_induction_on (P := fun S : X.Opens => HasCover p S) ⊤ isCompact_univ ?_ ?_
  · exact ⟨X, _, 𝟙 _, p, 𝟙 _, inferInstance, inferInstance, inferInstance, by simp, fun _ h => h.elim⟩
  · intro S _ W h
    have : IsAffine W.1 := W.2
    have := h.union (hasCover_affine p W.1.ι)
    rwa [Scheme.Opens.range_ι] at this

open GlobalTheory.Spread GlobalTheory.SpreadSep in

/- English proof (translation)
Take `⟨Y, P, π₀, q₀, q, _, _, _, w, H⟩` from `hasCover_univ p`. Use `replace H := fun y => H y trivial`. Establish `: IsLocallyNoetherian P` using `LocallyOfFiniteType.isLocallyNoetherian q`. Establish `: CompactSpace P` using `QuasiCompact.compactSpace_of_compactSpace q`. Establish `: IsNoetherian P` using `{}`.

Take `⟨U, Z, hU, hZ, eΔ⟩` from `isLocallyClosed_range H`. Set `s : (Finset V)ᵒᵖ` to `.op ∅`. Set `π : (bcDiagram q V).obj s ⟶ P` to `pullback.fst q _`. Establish `: QuasiCompact π` using `inferInstanceAs (QuasiCompact (pullback.fst q _))`. Set `O : P.Opens` to `⟨U, hU⟩`.

Set `O' : P.Opens` to `⟨Zᶜ, hZ.isOpen_compl⟩`. Establish `key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range q₀`. Rewrite using `[eΔ]`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z`.

Rewrite using `[not_not]`. Take `⟨j, f, hj⟩` from `exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V) (π ⁻¹ᵁ O) (π ⁻¹ᵁ O') (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _)) (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.i …`. Establish `e : (bcCone q V).π.app s ≫ π = pullback.fst q _` using `bcMap_fst _ _`. Rewrite using `[key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]`. Conclude with `(universallyClosed_snd_iff w H _).mp ‹_›)`.

Establish `e : (bcDiagram q V).map f ≫ π = pullback.fst q _` using `bcMap_fst _ _`. Rewrite `hj` using `[key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]`. Use `(universallyClosed_snd_iff w H _).mpr hj` as an intermediate fact. Conclude with `⟨j.unop, { }⟩`.
-/
theorem exists_finset_isProper (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    [UniversallyClosed (pullback.snd p (spMap (algebraMap k V)))] :
    ∃ s : Finset V, IsProper (pullback.snd p (spMap (algebraMap k (Algebra.adjoin k (s : Set V))))) := by
  classical
  obtain ⟨Y, P, π₀, q₀, q, _, _, _, w, H⟩ := hasCover_univ p
  replace H := fun y => H y trivial
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  obtain ⟨U, Z, hU, hZ, eΔ⟩ := isLocallyClosed_range H
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (bcDiagram q V).obj s ⟶ P := pullback.fst q _
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst q _))
  let O : P.Opens := ⟨U, hU⟩
  let O' : P.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range q₀ := by
    rw [eΔ]
    ext x
    change π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z
    rw [not_not]
  obtain ⟨j, f, hj⟩ := exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V)
    (π ⁻¹ᵁ O) (π ⁻¹ᵁ O')
    (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (by
      have e : (bcCone q V).π.app s ≫ π = pullback.fst q _ := bcMap_fst _ _
      rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]
      exact (universallyClosed_snd_iff w H _).mp ‹_›)
  have e : (bcDiagram q V).map f ≫ π = pullback.fst q _ := bcMap_fst _ _
  rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e] at hj
  have := (universallyClosed_snd_iff w H _).mpr hj
  exact ⟨j.unop, { }⟩

end GlobalTheory.ProperLimit
