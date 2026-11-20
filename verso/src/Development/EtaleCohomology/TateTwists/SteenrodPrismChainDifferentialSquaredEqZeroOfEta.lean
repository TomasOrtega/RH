import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

/- English proof (translation)
Take `⟨p, r, a, b⟩` from `z`. Consider the cases of `p with`. Consider the case `zero => simp [Pr.d₁]`. Consider the case `succ p`. Simplify using `only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]`.
-/
lemma push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases p with
  | zero => simp [Pr.d₁]
  | succ p =>
    simp only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

/- English proof (translation)
Take `⟨p, r, a, b⟩` from `z`. Consider the cases of `r with`. Consider the case `zero => simp [Pr.d₂]`. Consider the case `succ r`. Simplify using `only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]`.
-/
lemma push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases r with
  | zero => simp [Pr.d₂]
  | succ r =>
    simp only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

/- English proof (translation)
Simplify using `[Pr.push]`.
-/
lemma push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (n : ℤ) :
    Pr.push θ (Finsupp.single z n) = Finsupp.single ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ n := by
  simp [Pr.push]

/- English proof (translation)
Establish `: (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N)`. Use `Finsupp.lhom_ext fun z n => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul, map_add, push_d₁, push_d₂]`. Conclude with `LinearMap.congr_fun this c`.
-/
lemma d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  have : (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul,
      map_add, push_d₁, push_d₂]
  exact LinearMap.congr_fun this c

/- English proof (translation)
Introduce `N c`. Unfold `Pr.bd`. Simplify using `only [map_sum, map_zsmul, d_push]`.
-/
theorem steenrod_prism_chain_differential_squared_eq_zero_of_etale : leaf_dbd := by
  intro N c
  unfold Pr.bd
  simp only [map_sum, map_zsmul, d_push]

end LateralTheory.EtaleFoundations.SteenPf
