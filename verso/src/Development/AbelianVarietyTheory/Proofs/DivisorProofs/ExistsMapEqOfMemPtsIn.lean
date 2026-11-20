import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

namespace CxPts

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}

/- English proof (translation)
Establish `hle : W ≤ j ⁻¹ᵁ j ''ᵁ W` using `(j.preimage_image_eq W).ge`. Express the relevant statement in the definitionally equal form `valR (w.1 ≫ j) (j ''ᵁ W) _ = valR w.1 W g`. Rewrite using `[← valR_appLE w.1 j hle hw, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]`. Conclude with `valR_res w.1 le_rfl hw g`.
-/
theorem ev_appIso_inv (j : Y ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) (W : Y.Opens) (g : Γ(Y, W))
    {w : CxPts q σ} (hw : w ∈ ptsIn q σ W) :
    ev p σ (j ''ᵁ W) ((j.appIso W).inv.hom g) (PtsOver.map j hj _ w) = ev q σ W g w := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR (w.1 ≫ j) (j ''ᵁ W) _ = valR w.1 W g
  rw [← valR_appLE w.1 j hle hw, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res w.1 le_rfl hw g

/- English proof (translation)
Take `⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩` from `h`. Use `⟨j ''ᵁ W, ι, inferInstance, fun a => (j.appIso W).inv.hom (g a), Φ, O, ?_, h₂, ?_, h₄, ?_⟩` and prove the remaining obligations. Conclude with `mem_ptsIn.2 ⟨_, mem_ptsIn.1 h₁, rfl⟩`. Simplify `h₃` using `only [ev_appIso_inv j hj W _ h₁]`. Establish `he` using `PtsOver.isOpenEmbedding_map j hj (spMap σ)`.

Rewrite using `[EventuallyEq, ← he.map_nhds_eq, eventually_map]`. Use `filter_upwards [h₅, (isOpen_ptsIn W).mem_nhds h₁] with w e hw`. Simplify using `only [ev_appIso_inv j hj W _ hw]`. Conclude with `e`.
-/
theorem VInfAt.of_isOpenImmersion {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → F} {z : CxPts q σ}
    (h : VInfAt (fun w => f (PtsOver.map j hj _ w)) z) : VInfAt f (PtsOver.map j hj _ z) := by
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨j ''ᵁ W, ι, inferInstance, fun a => (j.appIso W).inv.hom (g a), Φ, O, ?_, h₂, ?_, h₄, ?_⟩
  · exact mem_ptsIn.2 ⟨_, mem_ptsIn.1 h₁, rfl⟩
  · simpa only [ev_appIso_inv j hj W _ h₁] using h₃
  · have he := PtsOver.isOpenEmbedding_map j hj (spMap σ)
    rw [EventuallyEq, ← he.map_nhds_eq, eventually_map]
    filter_upwards [h₅, (isOpen_ptsIn W).mem_nhds h₁] with w e hw
    simp only [ev_appIso_inv j hj W _ hw]
    exact e

/- English proof (translation)
Establish `H : Set.range y.1 ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hy (x := x) trivial`. Use `⟨⟨IsOpenImmersion.lift U.ι y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩` and prove the remaining obligations.

Rewrite using `[← hq, ← Category.assoc, IsOpenImmersion.lift_fac]`. Conclude with `y.2`.
-/
theorem exists_map_eq_of_mem_ptsIn {U : X.Opens} {q : U.toScheme ⟶ Sp k} (hq : U.ι ≫ p = q)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) : ∃ z : CxPts q σ, PtsOver.map U.ι hq _ z = y := by
  have H : Set.range y.1 ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hy (x := x) trivial
  refine ⟨⟨IsOpenImmersion.lift U.ι y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← hq, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

end CxPts

/- English proof (translation)
Introduce `σ`. Use `Met.isCInf_of_exists fun y => ?_` and prove the remaining obligations. Take `⟨U, hy, hs⟩` from `hl σ y`. Establish `hj : U.ι ≫ ρ ≫ p = (U.ι ≫ ρ) ≫ p` using `(Category.assoc _ _ _).symm`. Take `⟨z, rfl⟩` from `exists_map_eq_of_mem_ptsIn hj hy`.

Establish `hsm : SmoothOfRelativeDimension 1 ((U.ι ≫ ρ) ≫ p)` using `hj ▸ hs`. Establish `e (w : CxPts ((U.ι ≫ ρ) ≫ p) σ) : PtsOver.map ρ rfl _ (PtsOver.map U.ι hj _ w) = PtsOver.map (U.ι ≫ ρ) rfl _ w` using `Subtype.ext (Category.assoc _ _ _)`. Establish `hc` using `(h.met σ).isVB.mem_pick (PtsOver.map (U.ι ≫ ρ) rfl _ z)`. Generalize the expression as in `(h.met σ).isVB.pick (PtsOver.map (U.ι ≫ ρ) rfl _ z) = c at hc`. Establish `hc' : PtsOver.map ρ rfl _ (PtsOver.map U.ι hj _ z) ∈ ptsIn p σ c.U` using `(e z).symm ▸ hc`.

Use `⟨Chart.pull c (h.met σ).isVB ρ, hc', fun a b => ?_⟩` and prove the remaining obligations. Use `VInfAt.of_isOpenImmersion U.ι hj ?_` and prove the remaining obligations. Use `(H U.toScheme (U.ι ≫ ρ) hsm σ (Chart.pull c (h.met σ).isVB (U.ι ≫ ρ)) z hc a b).congr ?_` and prove the remaining obligations. Use `filter_upwards [(isOpen_ptsIn ((U.ι ≫ ρ) ⁻¹ᵁ c.U)).mem_nhds hc] with w hw`. Establish `hw' : PtsOver.map (U.ι ≫ ρ) rfl _ w ∈ ptsIn p σ c.U` using `hw`.

Establish `e₁` using `(h.met σ).pull_G ρ rfl c (z := PtsOver.map U.ι hj _ w) ((e w).symm ▸ hw')`. Establish `e₂` using `(h.met σ).pull_G (U.ι ≫ ρ) rfl c hw'`. Rewrite `e₁` using `[e w]`. Conclude with `congrFun (congrFun (e₁.trans e₂.symm) a) b`.
-/
theorem VMetric.IsCInfNorm.pull_isCInf_of_local {k : Type} [CommRing k] {X Y : Scheme.{0}}
    {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInfNorm) (ρ : Y ⟶ X)
    (hl : ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ), ∃ U : Y.Opens, y ∈ ptsIn (ρ ≫ p) σ U ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ ρ ≫ p)) : (h.pull ρ rfl).IsCInf := by
  intro σ
  refine Met.isCInf_of_exists fun y => ?_
  obtain ⟨U, hy, hs⟩ := hl σ y
  have hj : U.ι ≫ ρ ≫ p = (U.ι ≫ ρ) ≫ p := (Category.assoc _ _ _).symm
  obtain ⟨z, rfl⟩ := exists_map_eq_of_mem_ptsIn hj hy
  have hsm : SmoothOfRelativeDimension 1 ((U.ι ≫ ρ) ≫ p) := hj ▸ hs
  have e (w : CxPts ((U.ι ≫ ρ) ≫ p) σ) : PtsOver.map ρ rfl _ (PtsOver.map U.ι hj _ w) =
      PtsOver.map (U.ι ≫ ρ) rfl _ w := Subtype.ext (Category.assoc _ _ _)
  have hc := (h.met σ).isVB.mem_pick (PtsOver.map (U.ι ≫ ρ) rfl _ z)
  generalize (h.met σ).isVB.pick (PtsOver.map (U.ι ≫ ρ) rfl _ z) = c at hc
  have hc' : PtsOver.map ρ rfl _ (PtsOver.map U.ι hj _ z) ∈ ptsIn p σ c.U := (e z).symm ▸ hc
  refine ⟨Chart.pull c (h.met σ).isVB ρ, hc', fun a b => ?_⟩
  refine VInfAt.of_isOpenImmersion U.ι hj ?_
  refine (H U.toScheme (U.ι ≫ ρ) hsm σ (Chart.pull c (h.met σ).isVB (U.ι ≫ ρ)) z hc a b).congr ?_
  filter_upwards [(isOpen_ptsIn ((U.ι ≫ ρ) ⁻¹ᵁ c.U)).mem_nhds hc] with w hw
  have hw' : PtsOver.map (U.ι ≫ ρ) rfl _ w ∈ ptsIn p σ c.U := hw
  have e₁ := (h.met σ).pull_G ρ rfl c (z := PtsOver.map U.ι hj _ w) ((e w).symm ▸ hw')
  have e₂ := (h.met σ).pull_G (U.ι ≫ ρ) rfl c hw'
  rw [e w] at e₁
  exact congrFun (congrFun (e₁.trans e₂.symm) a) b

end GlobalTheory
