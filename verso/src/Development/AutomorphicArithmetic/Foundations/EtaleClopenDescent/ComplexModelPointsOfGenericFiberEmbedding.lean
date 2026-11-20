import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

/- English proof (translation)
Introduce `p _ D R _ _ b φ gb hρ ht N h3 hcop M X j hjo hjc hjs hg y' hy'`. Take `⟨o₁, ⟨e₁⟩⟩` from `GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp ℂ) M.s y' M.univ`. Establish `hs : y' ≫ M.s = 𝟙 (Sp ℂ) ≫ spMap φ` using `by rw [hy', Category.id_comp]`. Set `og : GObj gb N (𝟙 (Sp ℂ))` to `GenCmp.toGObj (GenCmp.rebase hρ ht hs o₁) (GenCmp.geomFull hcop _)`. Take `⟨f, ⟨hf, ⟨g⟩⟩, -⟩` from `X.rep (Sp ℂ) (𝟙 _) og`.

Set `O₂` to `GenCmp.toObj hρ ht X.univ (GenCmp.genericObject_kernelCondition _)`. Establish `e2 : ObjMap o₁ O₂ f` using `⟨g.φ, g.φ₂, g.cart, g.sq, g.act, g.pol, g.eta⟩`. Take `⟨φA, φ₂, hc, hsq, ha, ⟨hp⟩, he⟩` from `hg`. Establish `e3 : ObjMap O₂ M.univ (j ≫ pullback.fst _ _)` using `⟨φA, φ₂, hc, hsq, ha, hp, he⟩`. Take `⟨e4⟩` from `objMap_comp p D R b N (Sp ℂ) X.X M.X _ _ _ o₁ O₂ M.univ f _ e2 e3`.

Establish `hcomp : (f ≫ j ≫ pullback.fst M.s (spMap φ)) ≫ M.s = y' ≫ M.s`. Rewrite using `[hy']`. Simplify using `only [Category.assoc]`. Rewrite using `[pullback.condition, ← Category.assoc j, hjs, ← Category.assoc, hf, Category.id_comp]`. Establish `hfy : f ≫ j ≫ pullback.fst M.s (spMap φ) = y'`.

Take `⟨f', -, hu⟩` from `M.rep (Sp ℂ) (y' ≫ M.s) o₁`. Conclude with `(hu _ ⟨hcomp, ⟨e4⟩⟩).trans (hu y' ⟨rfl, ⟨e₁⟩⟩).symm`. Use `⟨f, ⟨hf, hfy⟩, fun y hy => ?_⟩` and prove the remaining obligations. Apply `(cancel_mono j).1` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc]`. Rewrite using `[hy.2, hfy]`. Simplify using `only [Category.assoc]`. Rewrite using `[hjs, hy.1, hf]`.
-/
theorem UpperTheory.Cb.complexModel_points_of_genericFiber_embedding :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (φ : R →+* ℂ) (gb : GBase D.toG ℂ), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N) (j : X.X ⟶ pullback M.s (spMap φ)), IsOpenImmersion j → IsClosedImmersion j → j ≫ pullback.snd _ _ = X.s → IsGPull X.univ M.univ (j ≫ pullback.fst _ _) → ∀ y' : Sp ℂ ⟶ M.X, y' ≫ M.s = spMap φ → ∃! y : Sp ℂ ⟶ X.X, y ≫ X.s = 𝟙 _ ∧ y ≫ j ≫ pullback.fst _ _ = y' := by
  intro p _ D R _ _ b φ gb hρ ht N h3 hcop M X j hjo hjc hjs hg y' hy'
  obtain ⟨o₁, ⟨e₁⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp ℂ) M.s y' M.univ
  have hs : y' ≫ M.s = 𝟙 (Sp ℂ) ≫ spMap φ := by rw [hy', Category.id_comp]
  let og : GObj gb N (𝟙 (Sp ℂ)) := GenCmp.toGObj (GenCmp.rebase hρ ht hs o₁) (GenCmp.geomFull hcop _)
  obtain ⟨f, ⟨hf, ⟨g⟩⟩, -⟩ := X.rep (Sp ℂ) (𝟙 _) og
  let O₂ := GenCmp.toObj hρ ht X.univ (GenCmp.genericObject_kernelCondition _)
  have e2 : ObjMap o₁ O₂ f := ⟨g.φ, g.φ₂, g.cart, g.sq, g.act, g.pol, g.eta⟩
  obtain ⟨φA, φ₂, hc, hsq, ha, ⟨hp⟩, he⟩ := hg
  have e3 : ObjMap O₂ M.univ (j ≫ pullback.fst _ _) := ⟨φA, φ₂, hc, hsq, ha, hp, he⟩
  obtain ⟨e4⟩ := objMap_comp p D R b N (Sp ℂ) X.X M.X _ _ _ o₁ O₂ M.univ f _ e2 e3
  have hcomp : (f ≫ j ≫ pullback.fst M.s (spMap φ)) ≫ M.s = y' ≫ M.s := by
    rw [hy']
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc j, hjs, ← Category.assoc, hf, Category.id_comp]
  have hfy : f ≫ j ≫ pullback.fst M.s (spMap φ) = y' := by
    obtain ⟨f', -, hu⟩ := M.rep (Sp ℂ) (y' ≫ M.s) o₁
    exact (hu _ ⟨hcomp, ⟨e4⟩⟩).trans (hu y' ⟨rfl, ⟨e₁⟩⟩).symm
  refine ⟨f, ⟨hf, hfy⟩, fun y hy => ?_⟩
  apply (cancel_mono j).1
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hy.2, hfy]
  · simp only [Category.assoc]
    rw [hjs, hy.1, hf]
