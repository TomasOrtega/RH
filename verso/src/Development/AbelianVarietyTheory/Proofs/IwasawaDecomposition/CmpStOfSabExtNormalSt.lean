import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.TorRef

/- English proof (translation)
Take `⟨PP', cub, sym, adj, prim, m, -⟩` from `sabPull Out.proved_CubePullSt f t`. Conclude with `⟨_, ⟨m⟩⟩`.
-/
theorem exists_sabMap_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m⟩⟩

/- English proof (translation)
Introduce `hS E _ _ _ H D l Xo c O O' _ _ β β' Y Z ρ hρ hN`. Use `isProper_genStr Z` as an intermediate fact. Establish `: IsLocallyNoetherian (gen Z)` using `LocallyOfFiniteType.isLocallyNoetherian (genStr Z)`. Take `⟨t₀, ⟨n₁⟩⟩` from `exists_sabMap_pull (genι Z) Z.t`. Take `⟨t', ⟨n'⟩⟩` from `exists_sabMap_pull (ρ ≫ genι Y) Y.t`.

Take `⟨a, ha⟩` from `GlobalTheory.LevelCover.sab_cancel n₁ Z.m Z.jQ rfl`. Take `⟨k, hk⟩` from `GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)`. Take `⟨ky, hky⟩` from `GlobalTheory.LevelCover.sab_comp k Y.m (e := Z.jQ ≫ ρ ≫ genι Y) (by rw [Category.id_comp, ← hρ, Category.assoc])`. Take `⟨a', ha'⟩` from `GlobalTheory.LevelCover.sab_cancel n' ky Z.jQ rfl`. Establish `hdom : IsDominant Z.jQ` using `⟨Z.jQ_dense⟩`.

Take `⟨b, hb⟩` from `hS E H (gen Z) (Xo.XF c) Z.jQ hN Z.jQ_open hdom Z.oF.t t₀ t' a a' Z.oF.proper`. Take `⟨n₂, hn₂⟩` from `GlobalTheory.LevelCover.sab_comp b n' (Category.id_comp _)`. Use `⟨t₀, n₁, n₂, fun T g g₁ g₂ h₁ h₂ h₃ h₄ => ?_⟩` and prove the remaining obligations. Establish `hg : g = g₁ ≫ a.φ`. Apply `n₁.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[h₂, Category.assoc, ha]`. Rewrite using `[h₁, Category.assoc, a.cart.1.w]`. Establish `hg₂ : g₁ ≫ k.φ = g₂`. Apply `Y.m0.toSABMap.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hk, h₃]`.

Rewrite using `[Category.assoc, k.cart.1.w, Category.comp_id, h₄]`. Rewrite using `[hn₂, hg]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hb, ha', hky, reassoc_of% hg₂]`.
-/
theorem cmpSt_of_sabExtNormalSt : SabExtNormalSt → CmpSt := by
  intro hS E _ _ _ H D l Xo c O O' _ _ β β' Y Z ρ hρ hN
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  obtain ⟨t₀, ⟨n₁⟩⟩ := exists_sabMap_pull (genι Z) Z.t
  obtain ⟨t', ⟨n'⟩⟩ := exists_sabMap_pull (ρ ≫ genι Y) Y.t
  obtain ⟨a, ha⟩ := GlobalTheory.LevelCover.sab_cancel n₁ Z.m Z.jQ rfl
  obtain ⟨k, hk⟩ := GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)
  obtain ⟨ky, hky⟩ := GlobalTheory.LevelCover.sab_comp k Y.m (e := Z.jQ ≫ ρ ≫ genι Y)
    (by rw [Category.id_comp, ← hρ, Category.assoc])
  obtain ⟨a', ha'⟩ := GlobalTheory.LevelCover.sab_cancel n' ky Z.jQ rfl
  have hdom : IsDominant Z.jQ := ⟨Z.jQ_dense⟩
  obtain ⟨b, hb⟩ := hS E H (gen Z) (Xo.XF c) Z.jQ hN Z.jQ_open hdom Z.oF.t t₀ t' a a' Z.oF.proper
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.LevelCover.sab_comp b n' (Category.id_comp _)
  refine ⟨t₀, n₁, n₂, fun T g g₁ g₂ h₁ h₂ h₃ h₄ => ?_⟩
  have hg : g = g₁ ≫ a.φ := by
    apply n₁.cart.1.hom_ext
    · rw [h₂, Category.assoc, ha]
    · rw [h₁, Category.assoc, a.cart.1.w]
  have hg₂ : g₁ ≫ k.φ = g₂ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hk, h₃]
    · rw [Category.assoc, k.cart.1.w, Category.comp_id, h₄]
  rw [hn₂, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ha', hky, reassoc_of% hg₂]

end GlobalTheory.TorRef
