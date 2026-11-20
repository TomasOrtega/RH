import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Cover

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]`.
-/
theorem comp_one_pt {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] (f : X ⟶ Y) : f ≫ (1 : Y ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

/- English proof (translation)
Introduce `R _ _ _ hB G _ _ hG O hO x`. Take `⟨hN, -, -, hC⟩` from `hB`. Establish `: Smooth G.hom` using `hG.smooth`. Establish `: GeometricallyConnected G.hom` using `hG.geomConnected`. Establish `hGI : GeometricallyIntegral G.hom` using `GlobalTheory.geometricallyIntegral_of_smooth G.hom`.

Establish `hη : ∀ P : Sp R, (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left P ∈ O`. Introduce `P`. Establish `hc : G.hom ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left (closedPoint R)) = closedPoint R`. Express the relevant statement in the definitionally equal form `((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R`. Rewrite using `[Over.w]`.

Both sides reduce to the same expression. Conclude with `((IsLocalRing.specializes_closedPoint P).map (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left.continuous).mem_open O.2 (hO _ hc)`. Distinguish the cases in `hx : G.hom x = closedPoint R`. Use `⟨η[G], ?_⟩` and prove the remaining obligations. Establish `: toUnit G ≫ (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1` using `(Hom.one_def).symm`.

Rewrite using `[this, _root_.mul_one]`. Conclude with `hO x hx`. Use `haveI := hN`. Set `k` to `G.left.residueField x`. Set `xp : Sp k ⟶ G.left` to `G.left.fromSpecResidueField x`.

Set `s : Sp k ⟶ Sp R` to `xp ≫ G.hom`. Establish `hrange : Set.range xp = {x}` using `Scheme.range_fromSpecResidueField x`. Establish `hxp : ∀ p, xp p = x` using `fun p => by`. Establish `h : xp p ∈ Set.range xp` using `⟨p, rfl⟩`. Rewrite `h` using `[hrange]`.

Conclude with `h`. Take `⟨p0⟩ : Nonempty (Sp k)` from `inferInstance`. Establish `hs : closedPoint R ∉ Set.range s`. Introduce and unpack `⟨p, hp⟩`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← hp, ← hxp p]`. Both sides reduce to the same expression. Establish `hirr : IrreducibleSpace (pullback G.hom s : Scheme.{0})`. Establish `: IsIntegral (pullback G.hom s)` using `hGI.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback _ _)`. Use `infer_instance`.

Set `Sx : Over (Sp R)` to `Over.mk s`. Set `T : Over (Sp R)` to `Over.mk (pullback.snd G.hom s ≫ s)`. Set `X' : Sx ⟶ G` to `Over.homMk xp rfl`. Set `p1 : T ⟶ G` to `Over.homMk (pullback.snd G.hom s ≫ xp) (by simp [T, s])`. Set `p2 : T ⟶ G` to `Over.homMk (pullback.fst G.hom s) (by simp [T, pullback.condition])`.

Set `m : T ⟶ G` to `p1 * p2`. Set `l : Sp k ⟶ pullback G.hom s` to `pullback.lift (X'⁻¹).left (𝟙 _) (by simpa [Sx] using Over.w (X'⁻¹))`. Establish `hl1 : l ≫ pullback.fst G.hom s = (X'⁻¹).left` using `pullback.lift_fst _ _ _`. Establish `hl2 : l ≫ pullback.snd G.hom s = 𝟙 _` using `pullback.lift_snd _ _ _`. Set `σ : Sx ⟶ T` to `Over.homMk l (by`.

Express the relevant statement in the definitionally equal form `l ≫ pullback.snd G.hom s ≫ s = s`. Rewrite using `[reassoc_of% hl2])`. Establish `hσ : σ ≫ m = 1`. Establish `e1 : σ ≫ p1 = X'`. Use `ext`.

Express the relevant statement in the definitionally equal form `l ≫ pullback.snd G.hom s ≫ xp = xp`. Rewrite using `[reassoc_of% hl2]`. Establish `e2 : σ ≫ p2 = X'⁻¹`. Use `ext`. Conclude with `hl1`.

Rewrite using `[comp_mul, e1, e2, _root_.mul_inv_cancel]`. Establish `hne : ((m.left ⁻¹ᵁ O : (pullback G.hom s).Opens) : Set (pullback G.hom s : Scheme.{0})).Nonempty`. Use `⟨σ.left p0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(σ.left ≫ m.left) p0 ∈ O`. Rewrite using `[← Over.comp_left, hσ, Hom.one_def, Over.comp_left]`.

Conclude with `hη _`. Establish `he : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 _` using `(Over.w _).trans (by simp)`. Take `⟨a, aΩ, ha, h1, h2, h3⟩` from `GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hC G ‹_› _ he k s hs hirr _ hne`. Set `A : 𝟙_ (Over (Sp R)) ⟶ G` to `Over.homMk a (ha.trans (by simp))`. Set `AΩ : Sx ⟶ T` to `Over.homMk aΩ (by simp [T, Sx, reassoc_of% h2])`.

Establish `f1 : AΩ ≫ p1 = X'` using `by ext; simp [AΩ, p1, X', reassoc_of% h2]`. Establish `f2 : AΩ ≫ p2 = toUnit Sx ≫ A` using `by ext; simp [AΩ, p2, A, h1, Sx]`. Establish `key : X' ≫ (𝟙 G * (toUnit G ≫ A)) = AΩ ≫ m`. Rewrite using `[comp_mul, comp_mul, f1, f2, Category.comp_id, comp_toUnit_assoc]`. Use `⟨A, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hxp p0]`. Express the relevant statement in the definitionally equal form `(X' ≫ (𝟙 G * (toUnit G ≫ A))).left p0 ∈ O`. Rewrite using `[key]`. Conclude with `h3 ⟨p0, rfl⟩`.
-/
theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ x : G.left, ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, (𝟙 G * (toUnit G ≫ a)).left x ∈ O := by
  intro R _ _ _ hB G _ _ hG O hO x
  obtain ⟨hN, -, -, hC⟩ := hB
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom

  have hη : ∀ P : Sp R, (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left P ∈ O := by
    intro P
    have hc : G.hom ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left (closedPoint R)) = closedPoint R := by
      change ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
      rw [Over.w]
      rfl
    exact ((IsLocalRing.specializes_closedPoint P).map (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left.continuous).mem_open
      O.2 (hO _ hc)
  by_cases hx : G.hom x = closedPoint R
  · refine ⟨η[G], ?_⟩
    have : toUnit G ≫ (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := (Hom.one_def).symm
    rw [this, _root_.mul_one]
    exact hO x hx

  haveI := hN
  let k := G.left.residueField x
  let xp : Sp k ⟶ G.left := G.left.fromSpecResidueField x
  let s : Sp k ⟶ Sp R := xp ≫ G.hom
  have hrange : Set.range xp = {x} := Scheme.range_fromSpecResidueField x
  have hxp : ∀ p, xp p = x := fun p => by
    have h : xp p ∈ Set.range xp := ⟨p, rfl⟩
    rw [hrange] at h
    exact h
  obtain ⟨p0⟩ : Nonempty (Sp k) := inferInstance
  have hs : closedPoint R ∉ Set.range s := by
    rintro ⟨p, hp⟩
    apply hx
    rw [← hp, ← hxp p]
    rfl
  have hirr : IrreducibleSpace (pullback G.hom s : Scheme.{0}) := by
    have : IsIntegral (pullback G.hom s) := hGI.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback _ _)
    infer_instance
  let Sx : Over (Sp R) := Over.mk s
  let T : Over (Sp R) := Over.mk (pullback.snd G.hom s ≫ s)
  let X' : Sx ⟶ G := Over.homMk xp rfl
  let p1 : T ⟶ G := Over.homMk (pullback.snd G.hom s ≫ xp) (by simp [T, s])
  let p2 : T ⟶ G := Over.homMk (pullback.fst G.hom s) (by simp [T, pullback.condition])
  let m : T ⟶ G := p1 * p2
  let l : Sp k ⟶ pullback G.hom s := pullback.lift (X'⁻¹).left (𝟙 _) (by simpa [Sx] using Over.w (X'⁻¹))
  have hl1 : l ≫ pullback.fst G.hom s = (X'⁻¹).left := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd G.hom s = 𝟙 _ := pullback.lift_snd _ _ _
  let σ : Sx ⟶ T := Over.homMk l (by
    change l ≫ pullback.snd G.hom s ≫ s = s
    rw [reassoc_of% hl2])
  have hσ : σ ≫ m = 1 := by
    have e1 : σ ≫ p1 = X' := by
      ext
      change l ≫ pullback.snd G.hom s ≫ xp = xp
      rw [reassoc_of% hl2]
    have e2 : σ ≫ p2 = X'⁻¹ := by
      ext
      exact hl1
    rw [comp_mul, e1, e2, _root_.mul_inv_cancel]
  have hne : ((m.left ⁻¹ᵁ O : (pullback G.hom s).Opens) : Set (pullback G.hom s : Scheme.{0})).Nonempty := by
    refine ⟨σ.left p0, ?_⟩
    change (σ.left ≫ m.left) p0 ∈ O
    rw [← Over.comp_left, hσ, Hom.one_def, Over.comp_left]
    exact hη _
  have he : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 _ := (Over.w _).trans (by simp)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hC G ‹_› _ he k s hs hirr _ hne
  let A : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a (ha.trans (by simp))
  let AΩ : Sx ⟶ T := Over.homMk aΩ (by simp [T, Sx, reassoc_of% h2])
  have f1 : AΩ ≫ p1 = X' := by ext; simp [AΩ, p1, X', reassoc_of% h2]
  have f2 : AΩ ≫ p2 = toUnit Sx ≫ A := by ext; simp [AΩ, p2, A, h1, Sx]
  have key : X' ≫ (𝟙 G * (toUnit G ≫ A)) = AΩ ≫ m := by
    rw [comp_mul, comp_mul, f1, f2, Category.comp_id, comp_toUnit_assoc]
  refine ⟨A, ?_⟩
  rw [← hxp p0]
  change (X' ≫ (𝟙 G * (toUnit G ≫ A))).left p0 ∈ O
  rw [key]
  exact h3 ⟨p0, rfl⟩

end GlobalTheory.Mum.Cover
