import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SteinPf
open LateralTheory.E.t_E2Cut

def RelNorm : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), IsIntegral T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g ∧
    ∀ V : T.Opens, IsAffineOpen V → (V : Set T).Nonempty →
      ((c ⁻¹ᵁ V : Set Z).Nonempty ∧ Function.Injective (c.app V) ∧
        ∀ b : Γ(Z, c ⁻¹ᵁ V), (c.app V).hom.IsIntegralElem b → ∃ a, c.app V a = b)

def AICOpen : Prop := ∀ {Z : Scheme.{0}}, AICSch Z → ∀ W : Z.Opens, (W : Set Z).Nonempty → AIC Γ(Z, W)

/- English proof (translation)
Introduce `p hm hd`. Take `⟨b, hb⟩` from `hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)`. Take `⟨a, rfl⟩` from `hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩`. Use `⟨a, hi ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← Polynomial.eval_map_apply]`.

Conclude with `hb`.
-/
theorem aic_of_int {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hB : AIC B) (hi : Function.Injective φ)
    (hc : ∀ b : B, φ.IsIntegralElem b → ∃ a, φ a = b) (hn : Nontrivial B) : AIC A := by
  intro p hm hd
  obtain ⟨b, hb⟩ := hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)
  obtain ⟨a, rfl⟩ := hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  refine ⟨a, hi ?_⟩
  rw [map_zero, ← Polynomial.eval_map_apply]; exact hb

/- English proof (translation)
Introduce `Z S g _ _ hZ`. Take `⟨T, c, k, hT, hc, hk, hck, hV⟩` from `hR g hZ`. Use `⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩` and prove the remaining obligations. Take `⟨hne', hi, hcl⟩` from `hV V hV' hne`. Establish `hB` using `hA hZ _ hne'`.

Establish `: IsIntegral Z` using `hZ.1`. Establish `: Nonempty (c ⁻¹ᵁ V)` using `hne'.to_subtype`. Conclude with `aic_of_int (c.app V).hom hB hi hcl inferInstance`.
-/
theorem Stein_of (hR : RelNorm) (hA : AICOpen) : Stein := by
  intro Z S g _ _ hZ
  obtain ⟨T, c, k, hT, hc, hk, hck, hV⟩ := hR g hZ
  refine ⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩
  obtain ⟨hne', hi, hcl⟩ := hV V hV' hne
  have hB := hA hZ _ hne'
  have : IsIntegral Z := hZ.1
  have : Nonempty (c ⁻¹ᵁ V) := hne'.to_subtype
  exact aic_of_int (c.app V).hom hB hi hcl inferInstance

end LateralTheory.E.SteinPf
