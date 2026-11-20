import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFinrankPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.SumInclusionOpen

variable {S : Scheme.{0}}

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := (snd T G).left) (h₂₂ := T.hom) (v₁₃ := G.hom) ?_ ?_ ?_` and prove the remaining obligations. Establish `h` using `(IsPullback.of_hasPullback T'.hom G.hom).flip`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`.

Consider the case `exact Over.w y`. Consider the case `(rw [Over.whiskerRight_left]; exact pullback.lift_snd _ _ _ |>.trans (Category.comp_id _))`. Consider the case `simp [Over.whiskerRight_left]`. Rewrite using `[Over.whiskerRight_left]`. Conclude with `pullback.lift_fst _ _ _`.

Conclude with `(IsPullback.of_hasPullback T.hom G.hom).flip`.
-/
private lemma sq {T T' G : Over S} (y : T' ⟶ T) :
    IsPullback (y ▷ G).left (fst T' G).left (fst T G).left y.left := by
  refine IsPullback.of_right (h₁₂ := (snd T G).left) (h₂₂ := T.hom) (v₁₃ := G.hom) ?_ ?_ ?_
  · have h := (IsPullback.of_hasPullback T'.hom G.hom).flip
    convert h using 1
    all_goals first
      | rfl
      | exact Over.w y
      | (rw [Over.whiskerRight_left]; exact pullback.lift_snd _ _ _ |>.trans (Category.comp_id _))
      | simp [Over.whiskerRight_left]
  · rw [Over.whiskerRight_left]
    exact pullback.lift_fst _ _ _
  · exact (IsPullback.of_hasPullback T.hom G.hom).flip

/- English proof (translation)
Use `ext1`. Simplify using `[MonoidalCategory.comp_whiskerRight, Set.preimage_comp]`.
-/
private lemma preim_comp {A B C G : Over S} (a : A ⟶ B) (b : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((a ≫ b) ▷ G).left ⁻¹ᵁ W = (a ▷ G).left ⁻¹ᵁ (b ▷ G).left ⁻¹ᵁ W := by
  ext1
  simp [MonoidalCategory.comp_whiskerRight, Set.preimage_comp]

/- English proof (translation)
Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := (fst T G).left) (g := y.left) x t h.symm`. Use `⟨(sq y).isoPullback.inv z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]`. Conclude with `hz`.
-/
private lemma exists_whisker {T T' G : Over S} (y : T' ⟶ T) (t : T'.left)
    (x : (T ⊗ G).left) (h : y.left t = (fst T G).left x) :
    ∃ z : (T' ⊗ G).left, (y ▷ G).left z = x := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (fst T G).left) (g := y.left) x t h.symm
  refine ⟨(sq y).isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hz

/- English proof (translation)
Use `SetLike.ext fun x => ?_` and prove the remaining obligations. Take `⟨i, a, ha⟩` from `hj ((fst T G).left x)`. Take `⟨z, rfl⟩` from `exists_whisker (j i) a x ha`. Use `congrArg (fun W => z ∈ W) (h i)` as an intermediate fact. Simplify using `using this`.
-/
private lemma opens_ext {ι : Type} {T G : Over S} {A : ι → Over S} (j : ∀ i, A i ⟶ T)
    (hj : ∀ t : T.left, ∃ i a, (j i).left a = t) (V V' : (T ⊗ G).left.Opens)
    (h : ∀ i, (j i ▷ G).left ⁻¹ᵁ V = (j i ▷ G).left ⁻¹ᵁ V') : V = V' := by
  refine SetLike.ext fun x => ?_
  obtain ⟨i, a, ha⟩ := hj ((fst T G).left x)
  obtain ⟨z, rfl⟩ := exists_whisker (j i) a x ha
  have := congrArg (fun W => z ∈ W) (h i)
  simpa using this

private instance whisker_open {T T' G : Over S} (y : T' ⟶ T) [IsOpenImmersion y.left] :
    IsOpenImmersion (y ▷ G).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq y).flip ‹_›

private noncomputable def sumObj (Y : ℕ → Over S) : Over S :=
  Over.mk (Sigma.desc fun r => (Y r).hom)

private noncomputable def sumι (Y : ℕ → Over S) (r : ℕ) : Y r ⟶ sumObj Y :=
  Over.homMk (Sigma.ι (fun r => (Y r).left) r) (by simp [sumObj])

private instance sumι_open (Y : ℕ → Over S) (r : ℕ) : IsOpenImmersion (sumι Y r).left :=
  inferInstanceAs (IsOpenImmersion (Sigma.ι (fun r => (Y r).left) r))

/- English proof (translation)
Take `⟨⟨r, a⟩, ha⟩` from `(sigmaMk (fun r => (Y r).left)).surjective p`. Conclude with `⟨r, a, by rw [← ha, sigmaMk_mk]; rfl⟩`.
-/
private lemma sumι_surj (Y : ℕ → Over S) (p : (sumObj Y).left) :
    ∃ r a, (sumι Y r).left a = p := by
  obtain ⟨⟨r, a⟩, ha⟩ := (sigmaMk (fun r => (Y r).left)).surjective p
  exact ⟨r, a, by rw [← ha, sigmaMk_mk]; rfl⟩

/- English proof (translation)
Conclude with `congrArg Sigma.fst ((sigmaι_eq_iff (fun r => (Y r).left) r s a b).mp h)`.
-/
private lemma sumι_disj (Y : ℕ → Over S) {r s : ℕ} {a : (Y r).left} {b : (Y s).left}
    (h : (sumι Y r).left a = (sumι Y s).left b) : r = s := by
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun r => (Y r).left) r s a b).mp h)

private noncomputable def sumU (G : Over S) (Y : ℕ → Over S)
    (U : ∀ r, (Y r ⊗ G).left.Opens) : (sumObj Y ⊗ G).left.Opens :=
  ⨆ r, (sumι Y r ▷ G).left ''ᵁ U r

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_apply, (sq y).w, Scheme.Hom.comp_apply]`.
-/
private lemma fst_whisker {T T' G : Over S} (y : T' ⟶ T) (z : (T' ⊗ G).left) :
    (fst T G).left ((y ▷ G).left z) = y.left ((fst T' G).left z) := by
  rw [← Scheme.Hom.comp_apply, (sq y).w, Scheme.Hom.comp_apply]

/- English proof (translation)
Use `SetLike.ext fun z => ?_` and prove the remaining obligations. Simplify using `only [sumU]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, w, hw, hwz⟩`.

Establish `hfst` using `congrArg (fst (sumObj Y) G).left hwz`. Rewrite `hfst` using `[fst_whisker, fst_whisker]`. Take `rfl` from `sumι_disj Y hfst`. Rewrite using `[← (sumι Y s ▷ G).left.isOpenEmbedding.injective hwz]` and apply the resulting hypothesis. Introduce `hz`.

Conclude with `⟨r, z, hz, rfl⟩`.
-/
private lemma preim_sumU (G : Over S) (Y : ℕ → Over S) (U : ∀ r, (Y r ⊗ G).left.Opens)
    (r : ℕ) : (sumι Y r ▷ G).left ⁻¹ᵁ sumU G Y U = U r := by
  refine SetLike.ext fun z => ?_
  simp only [sumU]
  simp
  constructor
  · rintro ⟨s, w, hw, hwz⟩
    have hfst := congrArg (fst (sumObj Y) G).left hwz
    rw [fst_whisker, fst_whisker] at hfst
    obtain rfl := sumι_disj Y hfst
    rwa [← (sumι Y s ▷ G).left.isOpenEmbedding.injective hwz]
  · intro hz
    exact ⟨r, z, hz, rfl⟩

/- English proof (translation)
Take `⟨r, t, ht⟩` from `sumι_surj Y ((fst _ G).left x)`. Conclude with `⟨r, exists_whisker _ t x ht⟩`.
-/
private lemma sum_cover (G : Over S) (Y : ℕ → Over S) (x : (sumObj Y ⊗ G).left) :
    ∃ r, ∃ a : (Y r ⊗ G).left, (sumι Y r ▷ G).left a = x := by
  obtain ⟨r, t, ht⟩ := sumι_surj Y ((fst _ G).left x)
  exact ⟨r, exists_whisker _ t x ht⟩

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff]`. Establish `e : (sumU G Y U : Set (sumObj Y ⊗ G).left)ᶜ = ⋃ r, (sumι Y r ▷ G).left '' (U r : Set (Y r ⊗ G).left)ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨r, a, rfl⟩` from `sum_cover G Y x`. Use `⟨r, a, fun ha => hx ?_, rfl⟩` and prove the remaining obligations. Establish `: a ∈ (sumι Y r ▷ G).left ⁻¹ᵁ sumU G Y U` using `by rw [preim_sumU]; exact ha`. Conclude with `this`.

Introduce and unpack `⟨r, a, ha, rfl⟩ hx`. Use `ha ?_` and prove the remaining obligations. Establish `: a ∈ (sumι Y r ▷ G).left ⁻¹ᵁ sumU G Y U` using `hx`. Rewrite `this` using `[preim_sumU]`. Conclude with `this`.

Rewrite using `[e]`. Conclude with `isOpen_iUnion fun r => (sumι Y r ▷ G).left.isOpenEmbedding.isOpenMap _ (hU r).isOpen_compl`.
-/
private lemma isClosed_sumU (G : Over S) (Y : ℕ → Over S) (U : ∀ r, (Y r ⊗ G).left.Opens)
    (hU : ∀ r, IsClosed (U r : Set (Y r ⊗ G).left)) :
    IsClosed (sumU G Y U : Set (sumObj Y ⊗ G).left) := by
  rw [← isOpen_compl_iff]
  have e : (sumU G Y U : Set (sumObj Y ⊗ G).left)ᶜ =
      ⋃ r, (sumι Y r ▷ G).left '' (U r : Set (Y r ⊗ G).left)ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      obtain ⟨r, a, rfl⟩ := sum_cover G Y x
      refine ⟨r, a, fun ha => hx ?_, rfl⟩
      have : a ∈ (sumι Y r ▷ G).left ⁻¹ᵁ sumU G Y U := by rw [preim_sumU]; exact ha
      exact this
    · rintro ⟨r, a, ha, rfl⟩ hx
      refine ha ?_
      have : a ∈ (sumι Y r ▷ G).left ⁻¹ᵁ sumU G Y U := hx
      rw [preim_sumU] at this
      exact this
  rw [e]
  exact isOpen_iUnion fun r =>
    (sumι Y r ▷ G).left.isOpenEmbedding.isOpenMap _ (hU r).isOpen_compl

private noncomputable def piece (T : Over S) (W : T.left.Opens) : Over S :=
  Over.mk (W.ι ≫ T.hom)

private noncomputable def pieceι (T : Over S) (W : T.left.Opens) : piece T W ⟶ T :=
  Over.homMk W.ι rfl

private instance pieceι_open (T : Over S) (W : T.left.Opens) :
    IsOpenImmersion (pieceι T W).left :=
  inferInstanceAs (IsOpenImmersion W.ι)

/- English proof (translation)
Use `top_le_iff.1 fun t _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hc t`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩`.
-/
private lemma piece_cover {T : Over S} (W : ℕ → T.left.Opens) (hc : ∀ t, ∃ r, t ∈ W r) :
    TopologicalSpace.IsOpenCover W := by
  refine top_le_iff.1 fun t _ => ?_
  obtain ⟨r, hr⟩ := hc t
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩

/- English proof (translation)
Use `ext1`. Use `Scheme.Cover.hom_ext (T.left.openCoverOfIsOpenCover W (piece_cover W hc)) _ _ fun (r : ℕ) => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W r).ι ≫ y.left = (W r).ι ≫ y'.left`. Use `congrArg (fun g => g.left) (h r)` as an intermediate fact. Conclude with `this`.
-/
private lemma piece_hom_ext {T Z : Over S} (W : ℕ → T.left.Opens) (hc : ∀ t, ∃ r, t ∈ W r)
    (y y' : T ⟶ Z) (h : ∀ r, pieceι T (W r) ≫ y = pieceι T (W r) ≫ y') : y = y' := by
  ext1
  refine Scheme.Cover.hom_ext (T.left.openCoverOfIsOpenCover W (piece_cover W hc)) _ _ fun (r : ℕ) => ?_
  change (W r).ι ≫ y.left = (W r).ι ≫ y'.left
  have := congrArg (fun g => g.left) (h r)
  exact this

/- English proof (translation)
Set `𝒰` to `T.left.openCoverOfIsOpenCover W (piece_cover W hc)`. Establish `hmem : ∀ (r : ℕ) (x : 𝒰.X r), (𝒰.f r) x ∈ W r`. Introduce `r x`. Express the relevant statement in the definitionally equal form `(W r).ι x ∈ W r`. Rewrite using `[← SetLike.mem_coe, ← Scheme.Opens.range_ι]`.

Conclude with `⟨x, rfl⟩`. Establish `hcompat : ∀ r s : ℕ, Limits.pullback.fst (𝒰.f r) (𝒰.f s) ≫ (f r).left = Limits.pullback.snd (𝒰.f r) (𝒰.f s) ≫ (f s).left`. Introduce `r s`. Distinguish the cases in `hrs : r = s`. Substitute `hrs haveI : Mono (𝒰.f r) := inferInstanceAs (Mono (W r).ι)` using the available equality.

Establish `e : Limits.pullback.fst (𝒰.f r) (𝒰.f r) = Limits.pullback.snd (𝒰.f r) (𝒰.f r)`. Rewrite using `[← cancel_mono (𝒰.f r)]`. Conclude with `Limits.pullback.condition`. Rewrite using `[e]`. Establish `: IsEmpty ↥(Limits.pullback (𝒰.f r) (𝒰.f s))`.

Use `⟨fun p => hrs ?_⟩` and prove the remaining obligations. Establish `h1` using `hmem r (Limits.pullback.fst (𝒰.f r) (𝒰.f s) p)`. Establish `h2` using `hmem s (Limits.pullback.snd (𝒰.f r) (𝒰.f s) p)`. Rewrite `h1`, `h2` using `[← Scheme.Hom.comp_apply]`. Rewrite `h1` using `[Limits.pullback.condition]`.

Conclude with `hd r s _ h1 h2`. Conclude with `isInitialOfIsEmpty.hom_ext _ _`. Set `g : T.left ⟶ Z.left` to `𝒰.glueMorphisms (fun r => (f r).left) hcompat`. Establish `hg : ∀ r : ℕ, (W r).ι ≫ g = (f r).left` using `fun r => 𝒰.ι_glueMorphisms _ hcompat r`. Establish `hw : g ≫ Z.hom = T.hom`.

Use `Scheme.Cover.hom_ext 𝒰 _ _ fun (r : ℕ) => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W r).ι ≫ g ≫ Z.hom = (W r).ι ≫ T.hom`. Rewrite using `[← Category.assoc, hg r]`. Conclude with `Over.w (f r)`. Use `⟨Over.homMk g hw, fun r => ?_⟩` and prove the remaining obligations.

Use `ext1`. Conclude with `hg r`.
-/
private lemma piece_glue {T Z : Over S} (W : ℕ → T.left.Opens) (hc : ∀ t, ∃ r, t ∈ W r)
    (hd : ∀ r s t, t ∈ W r → t ∈ W s → r = s) (f : ∀ r, piece T (W r) ⟶ Z) :
    ∃ y : T ⟶ Z, ∀ r, pieceι T (W r) ≫ y = f r := by
  let 𝒰 := T.left.openCoverOfIsOpenCover W (piece_cover W hc)
  have hmem : ∀ (r : ℕ) (x : 𝒰.X r), (𝒰.f r) x ∈ W r := by
    intro r x
    change (W r).ι x ∈ W r
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  have hcompat : ∀ r s : ℕ, Limits.pullback.fst (𝒰.f r) (𝒰.f s) ≫ (f r).left =
      Limits.pullback.snd (𝒰.f r) (𝒰.f s) ≫ (f s).left := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      haveI : Mono (𝒰.f r) := inferInstanceAs (Mono (W r).ι)
      have e : Limits.pullback.fst (𝒰.f r) (𝒰.f r) = Limits.pullback.snd (𝒰.f r) (𝒰.f r) := by
        rw [← cancel_mono (𝒰.f r)]
        exact Limits.pullback.condition
      rw [e]
    · have : IsEmpty ↥(Limits.pullback (𝒰.f r) (𝒰.f s)) := by
        refine ⟨fun p => hrs ?_⟩
        have h1 := hmem r (Limits.pullback.fst (𝒰.f r) (𝒰.f s) p)
        have h2 := hmem s (Limits.pullback.snd (𝒰.f r) (𝒰.f s) p)
        rw [← Scheme.Hom.comp_apply] at h1 h2
        rw [Limits.pullback.condition] at h1
        exact hd r s _ h1 h2
      exact isInitialOfIsEmpty.hom_ext _ _
  let g : T.left ⟶ Z.left := 𝒰.glueMorphisms (fun r => (f r).left) hcompat
  have hg : ∀ r : ℕ, (W r).ι ≫ g = (f r).left := fun r => 𝒰.ι_glueMorphisms _ hcompat r
  have hw : g ≫ Z.hom = T.hom := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun (r : ℕ) => ?_
    change (W r).ι ≫ g ≫ Z.hom = (W r).ι ≫ T.hom
    rw [← Category.assoc, hg r]
    exact Over.w (f r)
  refine ⟨Over.homMk g hw, fun r => ?_⟩
  ext1
  exact hg r

end UpperTheory.SumInclusionOpen

open UpperTheory.SumInclusionOpen in
/- English proof (translation)
Introduce `S G hfin het Y U hY`. Establish `hsumc` using `isClosed_sumU G Y U (fun r => (hY r).1)`. Use `⟨sumObj Y, sumU G Y U, hsumc, ?_⟩` and prove the remaining obligations. Introduce `T V hV`. Take `⟨hF, hE⟩` from `UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV`.

Set `φ : T.left → ℕ` to `Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj V)`. Establish `hlc : IsLocallyConstant φ` using `Scheme.Hom.isLocallyConstant_finrank _`. Set `W : ℕ → T.left.Opens` to `fun r => ⟨φ ⁻¹' {r}, hlc.isOpen_fiber r⟩`. Establish `hc : ∀ t, ∃ r, t ∈ W r` using `fun t => ⟨φ t, rfl⟩`. Establish `hd : ∀ r s t, t ∈ W r → t ∈ W s → r = s` using `fun r s t h1 h2 => h1.symm.trans h2`.

Establish `hmem : ∀ r (x : (piece T (W r)).left), φ ((pieceι T (W r)).left x) = r`. Introduce `r x`. Establish `: (pieceι T (W r)).left x ∈ W r`. Express the relevant statement in the definitionally equal form `(W r).ι x ∈ W r`. Rewrite using `[← SetLike.mem_coe, ← Scheme.Opens.range_ι]`.

Conclude with `⟨x, rfl⟩`. Conclude with `this`. Establish `hrank_sum : ∀ s (a : (Y s).left), Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj (sumU G Y U)) ((sumι Y s).left a) = s`. Introduce `s a`. Rewrite using `[← UpperTheory.clopProj_finrank_pullback (sumι Y s) (sumU G Y U) hfin het hsumc a, preim_sumU]`.

Conclude with `(hY s).2.1 a`. Establish `hVr_closed : ∀ r, IsClosed (((pieceι T (W r) ▷ G).left ⁻¹ᵁ V : (piece T (W r) ⊗ G).left.Opens) : Set (piece T (W r) ⊗ G).left)` using `fun r => IsClosed.preimage (Scheme.Hom.continuous (pieceι T (W r) ▷ G).left) hV`. Establish `hVr_rank : ∀ r (t : (piece T (W r)).left), Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj ((pieceι T (W r) ▷ G).left ⁻¹ᵁ V)) t = r`. Introduce `r t`. Rewrite using `[UpperTheory.clopProj_finrank_pullback (pieceι T (W r)) V hfin het hV t]`.

Conclude with `hmem r t`. Establish `hex : ∀ r, ∃ z : piece T (W r) ⟶ Y r, (z ▷ G).left ⁻¹ᵁ U r = (pieceι T (W r) ▷ G).left ⁻¹ᵁ V ∧ ∀ z' : piece T (W r) ⟶ Y r, (z' ▷ G).left ⁻¹ᵁ U r = (pieceι T (W r) ▷ G).left ⁻¹ᵁ V → z' = z` using `fun r => (hY r).2.2 _ _ (hVr_closed r) (hVr_rank r)`. Use `choose z hz hzu using hex`. Take `⟨y, hy⟩` from `piece_glue W hc hd (fun r => z r ≫ sumι Y r)`. Establish `hjs : ∀ t : T.left, ∃ r, ∃ a, (pieceι T (W r)).left a = t`.

Introduce `t`. Take `⟨r, hr⟩` from `hc t`. Establish `: t ∈ Set.range (W r).ι` using `by rw [Scheme.Opens.range_ι]; exact hr`. Take `⟨a, ha⟩` from `this`. Conclude with `⟨r, a, ha⟩`.

Establish `key : ∀ (y₀ : T ⟶ sumObj Y) r (z₀ : piece T (W r) ⟶ Y r), pieceι T (W r) ≫ y₀ = z₀ ≫ sumι Y r → (pieceι T (W r) ▷ G).left ⁻¹ᵁ ((y₀ ▷ G).left ⁻¹ᵁ sumU G Y U) = (z₀ ▷ G).left ⁻¹ᵁ U r`. Introduce `y₀ r z₀ h`. Rewrite using `[← preim_comp, h, preim_comp, preim_sumU]`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Apply `opens_ext (fun r => pieceι T (W r)) hjs` to reduce the goal to its premises.

Introduce `r`. Rewrite using `[key y r (z r) (hy r), hz r]`. Introduce `y' hy'`. Apply `piece_hom_ext W hc` to reduce the goal to its premises. Introduce `r`.

Rewrite using `[hy r]`. Establish `hrange : Set.range (pieceι T (W r) ≫ y').left ⊆ Set.range (sumι Y r).left`. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨s, a, ha⟩` from `sumι_surj Y ((pieceι T (W r) ≫ y').left t)`. Establish `e1 : φ ((pieceι T (W r)).left t) = r` using `hmem r t`.

Establish `e2 : φ ((pieceι T (W r)).left t) = s`. Express the relevant statement in the definitionally equal form `Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj V) _ = s`. Rewrite using `[← hy', UpperTheory.clopProj_finrank_pullback y' (sumU G Y U) hfin het hsumc]`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, ← ha]`. Conclude with `hrank_sum s a`.

Take `rfl : r = s` from `e1.symm.trans e2`. Conclude with `⟨a, ha⟩`. Set `l` to `IsOpenImmersion.lift (sumι Y r).left (pieceι T (W r) ≫ y').left hrange`. Establish `hl : l ≫ (sumι Y r).left = (pieceι T (W r) ≫ y').left` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hlw : l ≫ (Y r).hom = (piece T (W r)).hom`.

Establish `h1 : (sumι Y r).left ≫ (sumObj Y).hom = (Y r).hom` using `Over.w (sumι Y r)`. Rewrite using `[← h1, ← Category.assoc, hl]`. Conclude with `Over.w (pieceι T (W r) ≫ y')`. Set `z' : piece T (W r) ⟶ Y r` to `Over.homMk l hlw`. Establish `hz' : pieceι T (W r) ≫ y' = z' ≫ sumι Y r` using `by ext1`.

Conclude with `hl.symm`. Establish `hzz : z' = z r` using `hzu r z' (by rw [← key y' r z' hz', hy'])`. Rewrite using `[hz', hzz]`.
-/
theorem UpperTheory.exists_clopRep_of_clopRepOfRank :
    ∀ {S : Scheme.{0}} (G : Over S), IsFinite G.hom → Etale G.hom → ∀ (Y : ℕ → Over S) (U : ∀ r, (Y r ⊗ G).left.Opens), (∀ r, UpperTheory.RepresentationRank.RepOfRank r G (Y r) (U r)) → ∃ (Y' : Over S) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y' U' := by
  intro S G hfin het Y U hY
  have hsumc := isClosed_sumU G Y U (fun r => (hY r).1)
  refine ⟨sumObj Y, sumU G Y U, hsumc, ?_⟩
  intro T V hV
  obtain ⟨hF, hE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
  let φ : T.left → ℕ := Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj V)
  have hlc : IsLocallyConstant φ := Scheme.Hom.isLocallyConstant_finrank _
  let W : ℕ → T.left.Opens := fun r => ⟨φ ⁻¹' {r}, hlc.isOpen_fiber r⟩
  have hc : ∀ t, ∃ r, t ∈ W r := fun t => ⟨φ t, rfl⟩
  have hd : ∀ r s t, t ∈ W r → t ∈ W s → r = s := fun r s t h1 h2 => h1.symm.trans h2
  have hmem : ∀ r (x : (piece T (W r)).left), φ ((pieceι T (W r)).left x) = r := by
    intro r x
    have : (pieceι T (W r)).left x ∈ W r := by
      change (W r).ι x ∈ W r
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact this
  have hrank_sum : ∀ s (a : (Y s).left),
      Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj (sumU G Y U)) ((sumι Y s).left a) = s := by
    intro s a
    rw [← UpperTheory.clopProj_finrank_pullback (sumι Y s) (sumU G Y U) hfin het hsumc a, preim_sumU]
    exact (hY s).2.1 a
  have hVr_closed : ∀ r, IsClosed
      (((pieceι T (W r) ▷ G).left ⁻¹ᵁ V : (piece T (W r) ⊗ G).left.Opens) :
        Set (piece T (W r) ⊗ G).left) :=
    fun r => IsClosed.preimage (Scheme.Hom.continuous (pieceι T (W r) ▷ G).left) hV
  have hVr_rank : ∀ r (t : (piece T (W r)).left),
      Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj ((pieceι T (W r) ▷ G).left ⁻¹ᵁ V)) t = r := by
    intro r t
    rw [UpperTheory.clopProj_finrank_pullback (pieceι T (W r)) V hfin het hV t]
    exact hmem r t
  have hex : ∀ r, ∃ z : piece T (W r) ⟶ Y r, (z ▷ G).left ⁻¹ᵁ U r = (pieceι T (W r) ▷ G).left ⁻¹ᵁ V ∧
      ∀ z' : piece T (W r) ⟶ Y r, (z' ▷ G).left ⁻¹ᵁ U r = (pieceι T (W r) ▷ G).left ⁻¹ᵁ V → z' = z :=
    fun r => (hY r).2.2 _ _ (hVr_closed r) (hVr_rank r)
  choose z hz hzu using hex
  obtain ⟨y, hy⟩ := piece_glue W hc hd (fun r => z r ≫ sumι Y r)
  have hjs : ∀ t : T.left, ∃ r, ∃ a, (pieceι T (W r)).left a = t := by
    intro t
    obtain ⟨r, hr⟩ := hc t
    have : t ∈ Set.range (W r).ι := by rw [Scheme.Opens.range_ι]; exact hr
    obtain ⟨a, ha⟩ := this
    exact ⟨r, a, ha⟩
  have key : ∀ (y₀ : T ⟶ sumObj Y) r (z₀ : piece T (W r) ⟶ Y r),
      pieceι T (W r) ≫ y₀ = z₀ ≫ sumι Y r →
      (pieceι T (W r) ▷ G).left ⁻¹ᵁ ((y₀ ▷ G).left ⁻¹ᵁ sumU G Y U) = (z₀ ▷ G).left ⁻¹ᵁ U r := by
    intro y₀ r z₀ h
    rw [← preim_comp, h, preim_comp, preim_sumU]
  refine ⟨y, ?_, ?_⟩
  · apply opens_ext (fun r => pieceι T (W r)) hjs
    intro r
    rw [key y r (z r) (hy r), hz r]
  · intro y' hy'
    apply piece_hom_ext W hc
    intro r
    rw [hy r]
    have hrange : Set.range (pieceι T (W r) ≫ y').left ⊆ Set.range (sumι Y r).left := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨s, a, ha⟩ := sumι_surj Y ((pieceι T (W r) ≫ y').left t)
      have e1 : φ ((pieceι T (W r)).left t) = r := hmem r t
      have e2 : φ ((pieceι T (W r)).left t) = s := by
        change Scheme.Hom.finrank (UpperTheory.RepresentationRank.proj V) _ = s
        rw [← hy', UpperTheory.clopProj_finrank_pullback y' (sumU G Y U) hfin het hsumc]
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← ha]
        exact hrank_sum s a
      obtain rfl : r = s := e1.symm.trans e2
      exact ⟨a, ha⟩
    let l := IsOpenImmersion.lift (sumι Y r).left (pieceι T (W r) ≫ y').left hrange
    have hl : l ≫ (sumι Y r).left = (pieceι T (W r) ≫ y').left := IsOpenImmersion.lift_fac _ _ _
    have hlw : l ≫ (Y r).hom = (piece T (W r)).hom := by
      have h1 : (sumι Y r).left ≫ (sumObj Y).hom = (Y r).hom := Over.w (sumι Y r)
      rw [← h1, ← Category.assoc, hl]
      exact Over.w (pieceι T (W r) ≫ y')
    let z' : piece T (W r) ⟶ Y r := Over.homMk l hlw
    have hz' : pieceι T (W r) ≫ y' = z' ≫ sumι Y r := by
      ext1
      exact hl.symm
    have hzz : z' = z r := hzu r z' (by rw [← key y' r z' hz', hy'])
    rw [hz', hzz]
