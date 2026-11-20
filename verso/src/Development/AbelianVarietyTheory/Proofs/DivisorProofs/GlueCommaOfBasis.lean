import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

/- English proof (translation)
Introduce `R _ C _ C' _ F G _ _ H hcov hdir T s hs`. Establish `key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C) (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂)`. Introduce `t₁ t₂ u₁ u₂ S w₁ w₂`. Take `⟨n, b, hb, hb'⟩` from `hdir t₁ t₂ S w₁ w₂`. Use `sub_eq_zero.1 (sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)` and prove the remaining obligations.

Take `⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩` from `hb' i S' u' hi`. Establish `e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁))`. Rewrite using `[hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]`. Establish `e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂))`. Rewrite using `[hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]`.

Establish `e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂` using `Subsingleton.elim _ _`. Rewrite using `[map_sub, e1, e2, e3, sub_self]`. Take `⟨n, b, hb, hb'⟩` from `hcov T`. Establish `hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y`. Introduce `S u`.

Distinguish the cases in `h : ∃ i, IsUnit (mp F u (b i))`. Take `⟨i, hi⟩` from `h`. Take `⟨t, v, w, -⟩` from `hb' i S u hi`. Conclude with `⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩`. Conclude with `⟨0, fun h' ↦ absurd h' h⟩`.

Use `choose σ hσ using hex`. Take `⟨x, hx⟩` from `glue_std H hb σ fun S S' u ψ hp ↦ by`. Take `⟨t, v, w, e⟩` from `hσ S u hp`. Take `⟨i, hi⟩` from `hp`. Take `⟨t', v', w', e'⟩` from `hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩`.

Rewrite using `[← e, ← e', ← mp_comp]`. Conclude with `key _ _ _ _ _ _ _`. Use `⟨x, fun t u ↦ ?_⟩` and prove the remaining obligations. Establish `hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤`. Use `congrArg (Ideal.map (mp F u)) hb` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span, Ideal.map_top, ← Set.range_comp]`. Then use the resulting hypothesis. Use `sub_eq_zero.1 (sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)` and prove the remaining obligations. Establish `hi' : IsUnit (mp F (u ≫ ψ) (b i))` using `by rw [mp_comp]; exact hi`. Take `⟨t', v', w', e'⟩` from `hσ S' (u ≫ ψ) ⟨i, hi'⟩`. Rewrite using `[map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]`.
-/
theorem glue_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T s hs
  have key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂) := by
    intro t₁ t₂ u₁ u₂ S w₁ w₂
    obtain ⟨n, b, hb, hb'⟩ := hdir t₁ t₂ S w₁ w₂
    refine sub_eq_zero.1 (sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)
    obtain ⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩ := hb' i S' u' hi
    have e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]
    have e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]
    have e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov T
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t, v, w, -⟩ := hb' i S u hi
      exact ⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t, v, w, e⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩
    rw [← e, ← e', ← mp_comp]
    exact key _ _ _ _ _ _ _
  refine ⟨x, fun t u ↦ ?_⟩
  have hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine sub_eq_zero.1 (sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]

end GlobalTheory.CatCoh.Desc
