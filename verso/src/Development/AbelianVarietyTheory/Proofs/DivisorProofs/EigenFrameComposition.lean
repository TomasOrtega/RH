import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameTri

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z R R' R'' _ _ _ φ φ' φ'' x x' x'' f g k ψ χ t s hf hg`. Establish `hx : x'' = spMap (χ.comp ψ) ≫ x` using `by rw [hg.1, hf.1, ← Category.assoc, spMap_comp_spMap]`. Establish `hφ : φ'' = (χ.comp ψ).comp φ` using `by rw [hg.2.1, hf.2.1, RingHom.comp_assoc]`. Use `⟨hx, hφ, fun τ i => ?_⟩` and prove the remaining obligations. Take `⟨f', hf'⟩` from `f.exists_isMap ψ hf.2.1 hf.1`.

Take `⟨f'', hf''⟩` from `f'.exists_isMap χ hg.2.1 hg.1`. Take `⟨g'', hg''⟩` from `g.exists_isMap χ hg.2.1 hg.1`. Take `⟨hA, hAd⟩` from `EigFrame.Tri.co τ hf hf'`. Take `⟨hB, hBd⟩` from `EigFrame.Tri.co τ hg hg''`. Establish `hM : f''.co g'' τ = (f'.co g τ).map χ` using `EigFrame.IsMap.co τ hf'' hg'' hg.1`.

Establish `hQ : f''.co k τ = f''.co g'' τ * g''.co k τ` using `(f''.co_mul g'' k τ).symm`. Establish `hd : ∀ a j, j < a → (f'.co g τ).map χ a j = 0` using `fun a j h => by`. Rewrite using `[Matrix.map_apply, hA a j h, map_zero]`. Use `⟨fun a => f''.co k τ a i, ?_, fun a ha => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hQ, hM, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[Matrix.map_apply, hAd, hBd]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases.

Rewrite using `[hd i j h, zero_mul]`. Rewrite using `[hB j i h, mul_zero]`. Simplify using the standard rewrite rules. Simplify using `only`. Rewrite using `[hQ, hM, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `lt_or_ge j a with h | h` into its components or cases. Rewrite using `[hd a j h, zero_mul]`. Rewrite using `[hB j i (lt_of_lt_of_le ha h), mul_zero]`. Establish `e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = f''.v τ` using `funext fun j => by`.

Rewrite using `[hf'' τ j, hf' τ j, ← Category.assoc]`. Use `congr 1`. Establish `e2 : dualMap (χ.comp ψ) = (dualMap χ).comp (dualMap ψ)`. Apply the tactic sequence `ext r <;> simp [dualMap]`. Rewrite using `[e2]`.

Simplify using `[spMap, Spec.map_comp]`. Rewrite using `[e]`. Conclude with `f''.co_spec k τ i`.
-/
theorem tri_trans : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} (f : EigFrame Z φ x) (g : EigFrame Z φ' x') (k : EigFrame Z φ'' x'') (ψ : R →+* R') (χ : R' →+* R'') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R''ˣ), f.Tri ψ g t → g.Tri χ k s → f.Tri (χ.comp ψ) k (fun τ i => Units.map χ.toMonoidHom (t τ i) * s τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z R R' R'' _ _ _ φ φ' φ'' x x' x'' f g k ψ χ t s hf hg
  have hx : x'' = spMap (χ.comp ψ) ≫ x := by rw [hg.1, hf.1, ← Category.assoc, spMap_comp_spMap]
  have hφ : φ'' = (χ.comp ψ).comp φ := by rw [hg.2.1, hf.2.1, RingHom.comp_assoc]
  refine ⟨hx, hφ, fun τ i => ?_⟩
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨f'', hf''⟩ := f'.exists_isMap χ hg.2.1 hg.1
  obtain ⟨g'', hg''⟩ := g.exists_isMap χ hg.2.1 hg.1
  obtain ⟨hA, hAd⟩ := EigFrame.Tri.co τ hf hf'
  obtain ⟨hB, hBd⟩ := EigFrame.Tri.co τ hg hg''
  have hM : f''.co g'' τ = (f'.co g τ).map χ := EigFrame.IsMap.co τ hf'' hg'' hg.1
  have hQ : f''.co k τ = f''.co g'' τ * g''.co k τ := (f''.co_mul g'' k τ).symm
  have hd : ∀ a j, j < a → (f'.co g τ).map χ a j = 0 := fun a j h => by
    rw [Matrix.map_apply, hA a j h, map_zero]
  refine ⟨fun a => f''.co k τ a i, ?_, fun a ha => ?_, ?_⟩
  · dsimp only
    rw [hQ, hM, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.map_apply, hAd, hBd]; simp
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hd i j h, zero_mul]
      · rw [hB j i h, mul_zero]
    · simp
  · dsimp only
    rw [hQ, hM, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hd a j h, zero_mul]
    · rw [hB j i (lt_of_lt_of_le ha h), mul_zero]
  · have e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = f''.v τ := funext fun j => by
      rw [hf'' τ j, hf' τ j, ← Category.assoc]
      congr 1
      have e2 : dualMap (χ.comp ψ) = (dualMap χ).comp (dualMap ψ) := by
        ext r <;> simp [dualMap]
      rw [e2]
      simp [spMap, Spec.map_comp]
    rw [e]
    exact f''.co_spec k τ i

end GlobalTheory.FrameTri
