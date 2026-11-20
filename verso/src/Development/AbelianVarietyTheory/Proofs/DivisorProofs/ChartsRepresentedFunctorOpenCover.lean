import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `F Ix U x hinj hW hcov B x₀ hrep`. Establish `uniq : ∀ (T : Scheme.{0}) (g g' : T ⟶ B), F.map g.op x₀ = F.map g'.op x₀ → g = g'` using `fun T g g' h => (hrep T (F.map g'.op x₀)).unique h rfl`. Use `choose j hj using fun i => (hrep (U i) (x i)).exists`. Use `⟨j, fun i => ?_, fun p => ?_, hj⟩` and prove the remaining obligations. Take `⟨W, hWi⟩` from `hW i B x₀`.

Establish `hjW : Set.range (j i) ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `((hWi (U i) (j i)).1 ⟨𝟙 _, by rw [hj i]; simp⟩) q`. Take `⟨u, hu⟩` from `(hWi W.toScheme W.ι).2 (fun q => by`.

Establish `: W.ι q ∈ Set.range W.ι` using `⟨q, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι] at this)` and apply the resulting hypothesis. Use `set l := IsOpenImmersion.lift W.ι (j i) hjW with hldef`. Establish `hl : l ≫ W.ι = j i` using `IsOpenImmersion.lift_fac _ _ _`. Establish `huj : u ≫ j i = W.ι`.

Apply `uniq` to reduce the goal to its premises. Rewrite using `[op_comp, FunctorToTypes.map_comp_apply, hj i, hu]`. Establish `hlu : l ≫ u = 𝟙 _`. Apply `hinj i` to reduce the goal to its premises. Rewrite using `[op_comp, FunctorToTypes.map_comp_apply, ← hu, ← FunctorToTypes.map_comp_apply, ← op_comp, hl, hj i]`.

Simplify using the standard rewrite rules. Establish `hul : u ≫ l = 𝟙 _`. Rewrite using `[← cancel_mono W.ι, Category.assoc, hl, huj, Category.id_comp]`. Use `haveI : IsIso l := ⟨⟨u, hlu, hul⟩⟩`. Rewrite using `[← hl]`.

Use `infer_instance`. Take `⟨i, Y, a, u, ⟨q, rfl⟩, ha⟩` from `hcov B x₀ p`. Use `⟨i, u q, ?_⟩` and prove the remaining obligations. Establish `: a = u ≫ j i`. Apply `uniq` to reduce the goal to its premises.

Rewrite using `[ha, op_comp, FunctorToTypes.map_comp_apply, hj i]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem charts_represented_open_cover : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1) (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) → ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F Ix U x hinj hW hcov B x₀ hrep
  have uniq : ∀ (T : Scheme.{0}) (g g' : T ⟶ B), F.map g.op x₀ = F.map g'.op x₀ → g = g' :=
    fun T g g' h => (hrep T (F.map g'.op x₀)).unique h rfl
  choose j hj using fun i => (hrep (U i) (x i)).exists
  refine ⟨j, fun i => ?_, fun p => ?_, hj⟩
  · obtain ⟨W, hWi⟩ := hW i B x₀

    have hjW : Set.range (j i) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact ((hWi (U i) (j i)).1 ⟨𝟙 _, by rw [hj i]; simp⟩) q
    obtain ⟨u, hu⟩ := (hWi W.toScheme W.ι).2 (fun q => by
      have : W.ι q ∈ Set.range W.ι := ⟨q, rfl⟩
      rwa [Scheme.Opens.range_ι] at this)
    set l := IsOpenImmersion.lift W.ι (j i) hjW with hldef
    have hl : l ≫ W.ι = j i := IsOpenImmersion.lift_fac _ _ _
    have huj : u ≫ j i = W.ι := by
      apply uniq
      rw [op_comp, FunctorToTypes.map_comp_apply, hj i, hu]
    have hlu : l ≫ u = 𝟙 _ := by
      apply hinj i
      rw [op_comp, FunctorToTypes.map_comp_apply, ← hu, ← FunctorToTypes.map_comp_apply, ← op_comp, hl, hj i]
      simp
    have hul : u ≫ l = 𝟙 _ := by
      rw [← cancel_mono W.ι, Category.assoc, hl, huj, Category.id_comp]
    haveI : IsIso l := ⟨⟨u, hlu, hul⟩⟩
    rw [← hl]
    infer_instance
  · obtain ⟨i, Y, a, u, ⟨q, rfl⟩, ha⟩ := hcov B x₀ p
    refine ⟨i, u q, ?_⟩
    have : a = u ≫ j i := by
      apply uniq
      rw [ha, op_comp, FunctorToTypes.map_comp_apply, hj i]
    rw [this]
    rfl

end GlobalTheory
