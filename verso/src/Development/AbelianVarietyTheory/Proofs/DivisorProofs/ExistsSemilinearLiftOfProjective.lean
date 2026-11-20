import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

/- English proof (translation)
Introduce `R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq`. Use `choose m hmW hmq using hq`. Use `choose σ hσ using hπ`. Establish `key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x`. Introduce `r s x hx h`.

Use `hW (r - s) (by rw [map_sub, h, sub_self]) x hx` as an intermediate fact. Rewrite `this` using `[sub_smul, sub_eq_zero]`. Then use the resulting hypothesis. Set `f : P → R₀ →+ M` to `fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by`. Introduce `a b`. Rewrite using `[← add_smul]`.

Conclude with `key _ _ _ (hmW w) (by rw [map_add, hσ, hσ, hσ]))`. Establish `hf : ∀ w c, f w c = σ c • m w` using `fun _ _ => rfl`. Set `g : (P →₀ R₀) →+ M` to `Finsupp.liftAddHom f`. Establish `hg : ∀ w c, g (Finsupp.single w c) = σ c • m w`. Introduce `w c`.

Simplify using `only [g, Finsupp.liftAddHom_apply_single, hf]`. Establish `g1 : ∀ r x, g (π r • x) = r • g x`. Introduce `r x`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]`. Consider the case `single w c`. Rewrite using `[Finsupp.smul_single, hg, hg, smul_smul]`. Conclude with `key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])`. Establish `g2 : ∀ x, g x ∈ W`.

Introduce `x`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `W.add_mem ha hb`.

Consider the case `single w c => rw [hg]`. Conclude with `W.smul_mem _ (hmW w)`. Establish `g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x)`. Introduce `x`. Proceed by induction on `x using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]`. Consider the case `single w c`. Rewrite using `[hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]`. Both sides reduce to the same expression.

Take `⟨s, hs⟩` from `hP.out`. Use `⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r w show g (s (π r • w)) = r • g (s w)`. Rewrite using `[map_smul, g1]`. Introduce `w`.

Conclude with `g2 _`. Introduce `w show q (g (s w)) = v w`. Rewrite using `[g3, hs]`.
-/
theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add, hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
