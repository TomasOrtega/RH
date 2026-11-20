import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GenGlue

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (IsLocalRing.closedPoint K))) (specializes_iff_mem_closure.1 (h _ z))⟩`.
-/
lemma isDominant_of_spec {K : Type} [Field K] {W : Scheme.{0}} (v : Sp K ⟶ W)
    (h : ∀ (q : Sp K) (z : W), v q ⤳ z) : IsDominant v :=
  ⟨fun z => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (IsLocalRing.closedPoint K)))
    (specializes_iff_mem_closure.1 (h _ z))⟩

/- English proof (translation)
Introduce `Y P _ _ U hU f w hw`. Establish `hgp : ∀ q, gp Y q = genericPoint Y` using `fun q => by`. Take `rfl : q = IsLocalRing.closedPoint Y.functionField` from `Subsingleton.elim _ _`. Conclude with `Scheme.fromSpecStalk_closedPoint`. Establish `hgen : ∀ (V : Y.Opens) (y : Y), y ∈ V → genericPoint Y ∈ V` using `fun V y hy => ((genericPoint_spec Y).mem_open_set_iff V.2).2 ⟨y, trivial, hy⟩`.

Establish `hlift : ∀ V : Y.Opens, genericPoint Y ∈ V → ∃ l : Sp Y.functionField ⟶ V.toScheme, l ≫ V.ι = gp Y` using `fun V hV => ⟨IsOpenImmersion.lift V.ι (gp Y) (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[hgp]`. Conclude with `hV), IsOpenImmersion.lift_fac _ _ _⟩`.

Establish `hdom : ∀ (V : Y.Opens) (l : Sp Y.functionField ⟶ V.toScheme), l ≫ V.ι = gp Y → IsDominant l`. Introduce `V l hl`. Use `isDominant_of_spec l fun q z => ?_` and prove the remaining obligations. Rewrite using `[← V.ι.isOpenEmbedding.isInducing.specializes_iff]`. Establish `e1 : V.ι (l q) = gp Y q` using `by rw [← hl]; rfl`.

Rewrite using `[e1, hgp]`. Conclude with `(genericPoint_spec Y).specializes trivial`. Set `g : Y → Y.PartialMap P` to `fun y => ⟨U y, (U y).2.dense ⟨y, hU y⟩, f y⟩`. Establish `heq : ∀ y y', (g y).toRationalMap = (g y').toRationalMap`. Introduce `y y'`.

Rewrite using `[Scheme.PartialMap.toRationalMap_eq_iff]`. Set `V` to `U y ⊓ U y'`. Establish `hV : genericPoint Y ∈ V` using `⟨hgen _ y (hU y), hgen _ y' (hU y')⟩`. Take `⟨l, hl⟩` from `hlift V hV`. Use `haveI := hdom V l hl`.

Use `⟨V, V.2.dense ⟨_, hV⟩, inf_le_left, inf_le_right, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]`. Use `ext_of_isDominant l ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, hw y _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl]), hw y' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl])]`. Set `y0` to `genericPoint Y`.

Set `F` to `(g y0).toRationalMap`. Establish `htop : F.domain = ⊤` using `top_le_iff.1 fun z _ => Scheme.RationalMap.mem_domain.2 ⟨g z, hU z, heq z y0⟩`. Establish `htop' : F.toPartialMap.domain = ⊤` using `htop`. Set `k : Y ⟶ F.toPartialMap.domain.toScheme` to `IsOpenImmersion.lift F.toPartialMap.domain.ι (𝟙 Y) (by rw [Scheme.Opens.range_ι, htop']; simp)`. Establish `hk : k ≫ F.toPartialMap.domain.ι = 𝟙 Y` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hgpm : gp Y ≫ k ≫ F.toPartialMap.hom = w`. Take `⟨l, hl⟩` from `hlift (U y0) (hU y0)`. Establish `h2 : (g y0).domain.ι ≫ k = Y.homOfLE (g y0).le_domain_toRationalMap`. Apply `(cancel_mono F.toPartialMap.domain.ι).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, hk, Category.comp_id]`.

Conclude with `(Scheme.homOfLE_ι _ _).symm`. Rewrite using `[← hl]`. Rewrite using `[Category.assoc, reassoc_of% h2]`. Conclude with `(congrArg (l ≫ ·) (g y0).toPartialMap_toRationalMap_restrict).trans (hw y0 l hl)`. Use `⟨k ≫ F.toPartialMap.hom, fun y => ?_, hgpm⟩` and prove the remaining obligations.

Take `⟨l, hl⟩` from `hlift (U y) (hgen _ y (hU y))`. Use `haveI := hdom _ l hl`. Use `ext_of_isDominant l ?_` and prove the remaining obligations. Rewrite using `[reassoc_of% hl, hgpm, hw y l hl]`.
-/
theorem exists_glue : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) →
    ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P),
    (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) →
    ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  intro Y P _ _ U hU f w hw
  have hgp : ∀ q, gp Y q = genericPoint Y := fun q => by
    obtain rfl : q = IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : ∀ (V : Y.Opens) (y : Y), y ∈ V → genericPoint Y ∈ V := fun V y hy =>
    ((genericPoint_spec Y).mem_open_set_iff V.2).2 ⟨y, trivial, hy⟩
  have hlift : ∀ V : Y.Opens, genericPoint Y ∈ V →
      ∃ l : Sp Y.functionField ⟶ V.toScheme, l ≫ V.ι = gp Y := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (gp Y) (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨q, rfl⟩; rw [hgp]; exact hV), IsOpenImmersion.lift_fac _ _ _⟩
  have hdom : ∀ (V : Y.Opens) (l : Sp Y.functionField ⟶ V.toScheme), l ≫ V.ι = gp Y → IsDominant l := by
    intro V l hl
    refine isDominant_of_spec l fun q z => ?_
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e1 : V.ι (l q) = gp Y q := by rw [← hl]; rfl
    rw [e1, hgp]
    exact (genericPoint_spec Y).specializes trivial
  let g : Y → Y.PartialMap P := fun y => ⟨U y, (U y).2.dense ⟨y, hU y⟩, f y⟩
  have heq : ∀ y y', (g y).toRationalMap = (g y').toRationalMap := by
    intro y y'
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    let V := U y ⊓ U y'
    have hV : genericPoint Y ∈ V := ⟨hgen _ y (hU y), hgen _ y' (hU y')⟩
    obtain ⟨l, hl⟩ := hlift V hV
    haveI := hdom V l hl
    refine ⟨V, V.2.dense ⟨_, hV⟩, inf_le_left, inf_le_right, ?_⟩
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
    refine ext_of_isDominant l ?_
    rw [← Category.assoc, ← Category.assoc,
      hw y _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl]),
      hw y' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl])]
  let y0 := genericPoint Y
  let F := (g y0).toRationalMap
  have htop : F.domain = ⊤ :=
    top_le_iff.1 fun z _ => Scheme.RationalMap.mem_domain.2 ⟨g z, hU z, heq z y0⟩
  have htop' : F.toPartialMap.domain = ⊤ := htop
  let k : Y ⟶ F.toPartialMap.domain.toScheme := IsOpenImmersion.lift F.toPartialMap.domain.ι (𝟙 Y)
    (by rw [Scheme.Opens.range_ι, htop']; simp)
  have hk : k ≫ F.toPartialMap.domain.ι = 𝟙 Y := IsOpenImmersion.lift_fac _ _ _
  have hgpm : gp Y ≫ k ≫ F.toPartialMap.hom = w := by
    obtain ⟨l, hl⟩ := hlift (U y0) (hU y0)
    have h2 : (g y0).domain.ι ≫ k = Y.homOfLE (g y0).le_domain_toRationalMap := by
      apply (cancel_mono F.toPartialMap.domain.ι).1
      rw [Category.assoc, hk, Category.comp_id]
      exact (Scheme.homOfLE_ι _ _).symm
    rw [← hl]
    rw [Category.assoc, reassoc_of% h2]
    exact (congrArg (l ≫ ·) (g y0).toPartialMap_toRationalMap_restrict).trans (hw y0 l hl)
  refine ⟨k ≫ F.toPartialMap.hom, fun y => ?_, hgpm⟩
  obtain ⟨l, hl⟩ := hlift (U y) (hgen _ y (hU y))
  haveI := hdom _ l hl
  refine ext_of_isDominant l ?_
  rw [reassoc_of% hl, hgpm, hw y l hl]

end GlobalTheory.Desc.GenGlue
