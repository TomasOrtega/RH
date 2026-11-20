import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCoverStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

/- English proof (translation)
The claim follows from `disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)`.
-/
theorem opens_disjoint_of {Y : Scheme.{0}} {U U' : Y.Opens} (h : ∀ z, z ∈ U → z ∉ U') : Disjoint U U' :=
  disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)

/- English proof (translation)
Use `h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)` as an intermediate fact. Simplify using `using this`.
-/
theorem not_mem_of_disjoint {Y : Scheme.{0}} {U U' : Y.Opens} (h : Disjoint U U') {z : Y} (hz : z ∈ U)
    (hz' : z ∈ U') : False := by
  have := h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)
  simpa using this

/- English proof (translation)
Set `W : κ → T.left.Opens` to `fun i ↦ t.left ⁻¹ᵁ V i`. Set `Ti : κ → Over S` to `fun i ↦ Over.mk ((W i).ι ≫ T.hom)`. Set `w : ∀ i, Ti i ⟶ T` to `fun i ↦ Over.homMk (W i).ι`. Set `ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom)` to `fun i ↦ Over.homMk (t.left ∣_ V i) (by`. Simplify using `[Ti, W, morphismRestrict_ι_assoc])`.

Establish `hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t` using `fun i ↦ by ext1; simp [ti, w, W, morphismRestrict_ι]`. Establish `hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i))` using `fun i ↦ Model.fam_ev hN (w i)`. Use `choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)`. Establish `hWc : ⨆ i, (W i).ι.opensRange = ⊤`. Use `eq_top_iff.2 fun z _ ↦ ?_` and prove the remaining obligations.

Establish `: t.left z ∈ ⨆ i, V i` using `hV ▸ trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩`. Establish `hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange`. Introduce `i i' h`.

Use `opens_disjoint_of fun z hz hz' ↦ ?_` and prove the remaining obligations. Simplify using `only [Scheme.Opens.opensRange_ι, W] at hz hz'`. Conclude with `not_mem_of_disjoint (hVd h) hz hz'`. Take `⟨hT⟩` from `nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd`. Set `xl : T.left ⟶ Bt.left` to `Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left`.

Establish `hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left` using `fun i ↦ Cofan.IsColimit.fac hT _ i`. Establish `hxo : xl ≫ Bt.hom = T.hom` using `Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by`. Express the relevant statement in the definitionally equal form `(W i).ι ≫ _ = (W i).ι ≫ _`. Rewrite using `[reassoc_of% hxl i, Over.w (j i), Over.w (x i)]`. Both sides reduce to the same expression.

Set `xx : T ⟶ Bt` to `Over.homMk xl hxo`. Establish `wxx : ∀ i, w i ≫ xx = x i ≫ j i` using `fun i ↦ by ext1`. Simplify using `only [Over.comp_left, Over.homMk_left, w, xx]`. Conclude with `hxl i`. Establish `hxt : xx ≫ bt = t` using `by ext1`.

Use `Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W i).ι ≫ _ = (W i).ι ≫ _`. Establish `e : w i ≫ xx ≫ bt = w i ≫ t`. Rewrite using `[reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]`. Simplify `congrArg (fun q ↦ q.left) e` using `[w, xx]`.

Use `⟨xx, hxt, ?_⟩` and prove the remaining obligations. Establish `hNl` using `hN.isLB`. Use `(same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)` and prove the remaining obligations. Establish `hwo : ∀ i, IsOpenImmersion (w i).left` using `fun i ↦ by show IsOpenImmersion (W i).ι; infer_instance`. Establish `hwa : ∀ i, IsOpenImmersion (A ◁ w i).left` using `fun i ↦ (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1`.

Establish `hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i` using `fun i z ↦ by`. Use `(@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2` as an intermediate fact. Express the relevant statement in the definitionally equal form `z ∈ Set.range (A ◁ w i).left ↔ _`. Rewrite using `[this, Set.mem_preimage]`. Express the relevant statement in the definitionally equal form `_ ∈ Set.range (W i).ι ↔ _`.

Rewrite using `[Scheme.Opens.range_ι]`. Both sides reduce to the same expression. Rewrite using `[← sub_eq_zero]`. Use `GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_` and prove the remaining obligations. Use `eq_top_iff.2 fun z _ ↦ ?_` and prove the remaining obligations.

Establish `: t.left ((snd A T).left z) ∈ ⨆ i, V i` using `hV ▸ trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩`. Introduce `i i' h`. Use `opens_disjoint_of fun z hz hz' ↦ ?_` and prove the remaining obligations.

Conclude with `not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')`. Rewrite using `[map_sub, pull_evc, pull_evc, sub_eq_zero]`. Simplify using `only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]`. Rewrite using `[wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]`. Conclude with `(cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2`.
-/
theorem rep_exists {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVd : Pairwise fun i i' => Disjoint (V i) (V i'))
    (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left]
    (hj : ⨆ i, (j i).left.opensRange = ⊤)
    (hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange)
    (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X) (hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι)
    (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Rep A (b i) (P i)) (hPt : Pt.IsLB)
    (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left)
    (hN : Fam A N) : ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  let W : κ → T.left.Opens := fun i ↦ t.left ⁻¹ᵁ V i
  let Ti : κ → Over S := fun i ↦ Over.mk ((W i).ι ≫ T.hom)
  let w : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (W i).ι
  let ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom) := fun i ↦ Over.homMk (t.left ∣_ V i) (by
    simp [Ti, W, morphismRestrict_ι_assoc])
  have hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t := fun i ↦ by
    ext1; simp [ti, w, W, morphismRestrict_ι]
  have hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i)) := fun i ↦ Model.fam_ev hN (w i)
  choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)
  have hWc : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left z ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩
  have hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange := by
    intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    simp only [Scheme.Opens.opensRange_ι, W] at hz hz'
    exact not_mem_of_disjoint (hVd h) hz hz'
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd
  let xl : T.left ⟶ Bt.left := Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left
  have hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left := fun i ↦ Cofan.IsColimit.fac hT _ i
  have hxo : xl ≫ Bt.hom = T.hom := Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by
    change (W i).ι ≫ _ = (W i).ι ≫ _
    rw [reassoc_of% hxl i, Over.w (j i), Over.w (x i)]
    rfl
  let xx : T ⟶ Bt := Over.homMk xl hxo
  have wxx : ∀ i, w i ≫ xx = x i ≫ j i := fun i ↦ by
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, xx]
    exact hxl i
  have hxt : xx ≫ bt = t := by
    ext1
    refine Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_
    change (W i).ι ≫ _ = (W i).ι ≫ _
    have e : w i ≫ xx ≫ bt = w i ≫ t := by
      rw [reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]
    simpa [w, xx] using congrArg (fun q ↦ q.left) e
  refine ⟨xx, hxt, ?_⟩
  have hNl := hN.isLB
  refine (same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)
  have hwo : ∀ i, IsOpenImmersion (w i).left := fun i ↦ by
    show IsOpenImmersion (W i).ι; infer_instance
  have hwa : ∀ i, IsOpenImmersion (A ◁ w i).left := fun i ↦
    (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1
  have hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i := fun i z ↦ by
    have := (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2
    change z ∈ Set.range (A ◁ w i).left ↔ _
    rw [this, Set.mem_preimage]
    change _ ∈ Set.range (W i).ι ↔ _
    rw [Scheme.Opens.range_ι]
    rfl
  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left ((snd A T).left z) ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩
  · intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    exact not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')
  · rw [map_sub, pull_evc, pull_evc, sub_eq_zero]
    simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]
    rw [wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]
    exact (cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2

end GlobalTheory.DualCon.ProdGlue
