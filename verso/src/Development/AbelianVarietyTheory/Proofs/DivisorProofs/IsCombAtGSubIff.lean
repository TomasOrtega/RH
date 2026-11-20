import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombSub

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

/- English proof (translation)
Apply the tactic sequence `ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsMul_zero_eq :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Set `q : tEpsG x0 ⟶ Over.mk x0` to `Over.homMk (spMap (algebraMap S (DualNumber S))) rfl`. Establish `e : spMap (epsMul (0 : S)) = spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom`. Rewrite using `[spMap_comp_spMap, epsMul_zero_eq]`. Rewrite using `[e, Category.assoc, h.2, ← MonObj.comp_one q]`. Both sides reduce to the same expression.
-/
theorem eps_zero_comp {v : Sp (DualNumber S) ⟶ t.G.left} (h : IsTanAtG t x0 v) :
    spMap (epsMul (0 : S)) ≫ v = (1 : tEpsG x0 ⟶ t.G).left := by
  let q : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have e : spMap (epsMul (0 : S)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
    rw [spMap_comp_spMap, epsMul_zero_eq]
  rw [e, Category.assoc, h.2, ← MonObj.comp_one q]
  rfl

/- English proof (translation)
Establish `key : ∀ u : Fin r → (tEpsG x0 ⟶ t.G), (∀ i, (u i).left = spMap (epsMul (a i)) ≫ v i) → (List.ofFn fun k => u (σ k)).prod = (List.ofFn u).prod`. Introduce `u hu`. Rewrite using `[List.prod_ofFn, List.prod_ofFn]`. Use `Fintype.prod_of_injective σ hσ _ _ (fun j hj => ?_) (fun _ => rfl)` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hu j, ha j hj, eps_zero_comp t x0 (hv j)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hw⟩`. Conclude with `⟨fun k => u (σ k), fun k => hu (σ k), by rw [key u hu, hw]⟩`. Introduce and unpack `⟨u, hu, hw⟩`.

Establish `hU : ∀ i, (Function.extend σ u (fun _ => 1) i).left = spMap (epsMul (a i)) ≫ v i`. Introduce `i`. Distinguish the cases in `hi : i ∈ Set.range σ`. Take `⟨k, rfl⟩` from `hi`. Rewrite using `[hσ.extend_apply]`.

Conclude with `hu k`. Rewrite using `[Function.extend_apply' _ _ _ hi, ha i hi, eps_zero_comp t x0 (hv i)]`. Use `⟨_, hU, ?_⟩` and prove the remaining obligations. Rewrite using `[← key _ hU, ← hw]`. Simplify using `only [hσ.extend_apply]`.
-/
theorem isCombAtG_sub_iff {r r' : ℕ} (σ : Fin r' → Fin r) (hσ : Function.Injective σ)
    (v : Fin r → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ j, IsTanAtG t x0 (v j)) (a : Fin r → S)
    (ha : ∀ j, j ∉ Set.range σ → a j = 0) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x0 v a w ↔ IsCombAtG t x0 (fun k => v (σ k)) (fun k => a (σ k)) w := by
  classical
  have key : ∀ u : Fin r → (tEpsG x0 ⟶ t.G), (∀ i, (u i).left = spMap (epsMul (a i)) ≫ v i) →
      (List.ofFn fun k => u (σ k)).prod = (List.ofFn u).prod := by
    intro u hu
    rw [List.prod_ofFn, List.prod_ofFn]
    refine Fintype.prod_of_injective σ hσ _ _ (fun j hj => ?_) (fun _ => rfl)
    apply Over.OverMorphism.ext
    rw [hu j, ha j hj, eps_zero_comp t x0 (hv j)]
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨fun k => u (σ k), fun k => hu (σ k), by rw [key u hu, hw]⟩
  · rintro ⟨u, hu, hw⟩
    have hU : ∀ i, (Function.extend σ u (fun _ => 1) i).left = spMap (epsMul (a i)) ≫ v i := by
      intro i
      by_cases hi : i ∈ Set.range σ
      · obtain ⟨k, rfl⟩ := hi
        rw [hσ.extend_apply]
        exact hu k
      · rw [Function.extend_apply' _ _ _ hi, ha i hi, eps_zero_comp t x0 (hv i)]
    refine ⟨_, hU, ?_⟩
    rw [← key _ hU, ← hw]
    simp only [hσ.extend_apply]

end GlobalTheory.CombSub
