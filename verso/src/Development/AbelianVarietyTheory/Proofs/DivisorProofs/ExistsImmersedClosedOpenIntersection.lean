import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

/- English proof (translation)
Introduce `Y _ Z₁ Z₂ ι₁ ι₂ U h₁ h₂`. Set `p : pullback ι₁ ι₂ ⟶ Y` to `pullback.fst ι₁ ι₂ ≫ ι₁`. Set `V : (pullback ι₁ ι₂).Opens` to `p ⁻¹ᵁ U`. Set `j : V.toScheme ⟶ Y` to `V.ι ≫ p`. Establish `hj : IsImmersion j` using `IsImmersion.comp _ _`.

Establish `hW : IsLocallyNoetherian V.toScheme` using `LocallyOfFiniteType.isLocallyNoetherian j`. Establish `hN : TopologicalSpace.NoetherianSpace V.toScheme` using `(IsPreimmersion.isEmbedding j).isInducing.noetherianSpace`. Use `⟨V.toScheme, j, hj, quasiCompact_of_noetherianSpace_source j, hW, ?_⟩` and prove the remaining obligations. Introduce `T g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hU⟩`. Set `f : T ⟶ pullback ι₁ ι₂` to `pullback.lift w₁ w₂ (hw₁.trans hw₂.symm)`. Establish `hf : f ≫ p = g`. Simplify using `only [f, p]`. Rewrite using `[← Category.assoc, pullback.lift_fst]`.

Conclude with `hw₁`. Establish `hr : Set.range f ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨τ, rfl⟩`. Use `show p (f τ) ∈ U`.

Rewrite using `[← Scheme.Hom.comp_apply, hf]`. Conclude with `hU τ`. Use `⟨IsOpenImmersion.lift V.ι f hr, ?_⟩` and prove the remaining obligations. Simplify using `only [j, ← Category.assoc, IsOpenImmersion.lift_fac, hf]`. Introduce and unpack `⟨w, rfl⟩`.

Use `⟨⟨w ≫ V.ι ≫ pullback.fst ι₁ ι₂, by simp [j, p]⟩, ⟨w ≫ V.ι ≫ pullback.snd ι₁ ι₂, by simp [j, p, pullback.condition]⟩, ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `: V.ι (w τ) ∈ V`. Establish `h` using `Scheme.Opens.range_ι V`. Conclude with `(Set.ext_iff.mp h (V.ι (w τ))).mp ⟨_, rfl⟩`.

Conclude with `this`.
-/
theorem GlobalTheory.HomFixMat.exists_immersed_locus : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  intro Y _ Z₁ Z₂ ι₁ ι₂ U h₁ h₂
  let p : pullback ι₁ ι₂ ⟶ Y := pullback.fst ι₁ ι₂ ≫ ι₁
  let V : (pullback ι₁ ι₂).Opens := p ⁻¹ᵁ U
  let j : V.toScheme ⟶ Y := V.ι ≫ p
  have hj : IsImmersion j := IsImmersion.comp _ _
  have hW : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian j
  have hN : TopologicalSpace.NoetherianSpace V.toScheme :=
    (IsPreimmersion.isEmbedding j).isInducing.noetherianSpace
  refine ⟨V.toScheme, j, hj, quasiCompact_of_noetherianSpace_source j, hW, ?_⟩
  intro T g
  constructor
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hU⟩
    let f : T ⟶ pullback ι₁ ι₂ := pullback.lift w₁ w₂ (hw₁.trans hw₂.symm)
    have hf : f ≫ p = g := by
      simp only [f, p]; rw [← Category.assoc, pullback.lift_fst]; exact hw₁
    have hr : Set.range f ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      show p (f τ) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact hU τ
    refine ⟨IsOpenImmersion.lift V.ι f hr, ?_⟩
    simp only [j, ← Category.assoc, IsOpenImmersion.lift_fac, hf]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w ≫ V.ι ≫ pullback.fst ι₁ ι₂, by simp [j, p]⟩,
      ⟨w ≫ V.ι ≫ pullback.snd ι₁ ι₂, by simp [j, p, pullback.condition]⟩, ?_⟩
    intro τ
    have : V.ι (w τ) ∈ V := by
      have h := Scheme.Opens.range_ι V
      exact (Set.ext_iff.mp h (V.ι (w τ))).mp ⟨_, rfl⟩
    exact this
