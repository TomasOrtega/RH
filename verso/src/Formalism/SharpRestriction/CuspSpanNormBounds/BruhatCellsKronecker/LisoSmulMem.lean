import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

/- English proof (translation)
Establish `h : (o : E) • v = o • v` using `algebraMap_smul E o v`. Rewrite using `[h]`. Conclude with `Λ.smul_mem o hv`.
-/
theorem liso_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (Λ : Submodule (𝓞 E) S.V)
    (o : 𝓞 E) {v : S.V} (hv : v ∈ Λ) : (o : E) • v ∈ Λ := by
  have h : (o : E) • v = o • v := algebraMap_smul E o v
  rw [h]
  exact Λ.smul_mem o hv

/- English proof (translation)
Introduce `E _ _ _ S Λ X hcm hlat huni hiso`. Take `⟨P0, hid, hX, hint⟩` from `h2 E S Λ X hlat`. Take `⟨P0', hadj, hint'⟩` from `h1 E S Λ huni P0 hint`. Take `⟨θ, hθ⟩` from `h3 E hcm`. Establish `hbar : star (θ : E) = ((1 - θ : 𝓞 E) : E)`.

Establish `: ((1 - θ : 𝓞 E) : E) = 1 - (θ : E)` using `by simp`. Rewrite using `[this]`. Take the linear combination `hθ`. Establish `hrev : ∀ x y, S.hT (P0' x) y = S.hT x (P0 y)`. Introduce `x y`.

Rewrite using `[← S.herm.eq y (P0' x), ← hadj y x, S.herm.eq]`. Establish `hHX : ∀ y, P0 (P0' y) ∈ X` using `fun y => hX _`. Establish `hHH : ∀ x y, S.hT (P0 (P0' x)) y = S.hT x (P0 (P0' y))`. Introduce `x y`. Rewrite using `[hadj, hrev]`.

Establish `hzero : ∀ x ∈ X, P0' x = 0`. Introduce `x hx`. Use `S.nondeg.2 _ (fun w => ?_)` and prove the remaining obligations. Rewrite using `[← hadj]`. Conclude with `hiso _ (hX w) _ hx`.

Use `⟨P0 - (θ : E) • (P0 ∘ₗ P0'), P0' - star (θ : E) • (P0 ∘ₗ P0'), ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]`. Rewrite using `[hadj, hHH]`. Introduce `x hx`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[hzero x hx, map_zero, smul_zero, sub_zero, hid x hx]`. Introduce `y`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]`. Conclude with `X.sub_mem (hX y) (X.smul_mem _ (hHX y))`.

Introduce `l hl`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]`. Conclude with `Λ.sub_mem (hint l hl) (liso_smul_mem Λ θ (hint _ (hint' l hl)))`. Introduce `l hl`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]`.

Rewrite using `[hbar]`. Conclude with `Λ.sub_mem (hint' l hl) (liso_smul_mem Λ (1 - θ) (hint _ (hint' l hl)))`. Introduce `w y`. Establish `e1 : S.hT (P0' w) (P0' y) = S.hT w (P0 (P0' y))` using `hrev _ _`. Establish `e2 : S.hT (P0' w) (P0 (P0' y)) = S.hT w (P0 (P0' y))`.

Rewrite using `[hrev, hid _ (hHX y)]`. Establish `e3 : S.hT (P0 (P0' w)) (P0' y) = S.hT w (P0 (P0' y))`. Rewrite using `[← hadj, hid _ (hHX w), hHH]`. Establish `e4 : S.hT (P0 (P0' w)) (P0 (P0' y)) = 0` using `hiso _ (hHX w) _ (hHX y)`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star, RingHom.id_apply]`.

Rewrite using `[e1, e2, e3, e4]`. Take the linear combination `(-(S.hT w (P0 (P0' y)))) * hθ`.
-/
theorem l_iso (h1 : IntegralAdjointUnimodular) (h2 : IntegralRetraction) (h3 : IntegralTraceSurjective) : IsotropicIntegralRetraction := by
  intro E _ _ _ S Λ X hcm hlat huni hiso
  obtain ⟨P0, hid, hX, hint⟩ := h2 E S Λ X hlat
  obtain ⟨P0', hadj, hint'⟩ := h1 E S Λ huni P0 hint
  obtain ⟨θ, hθ⟩ := h3 E hcm
  have hbar : star (θ : E) = ((1 - θ : 𝓞 E) : E) := by
    have : ((1 - θ : 𝓞 E) : E) = 1 - (θ : E) := by simp
    rw [this]
    linear_combination hθ

  have hrev : ∀ x y, S.hT (P0' x) y = S.hT x (P0 y) := by
    intro x y
    rw [← S.herm.eq y (P0' x), ← hadj y x, S.herm.eq]
  have hHX : ∀ y, P0 (P0' y) ∈ X := fun y => hX _
  have hHH : ∀ x y, S.hT (P0 (P0' x)) y = S.hT x (P0 (P0' y)) := by
    intro x y
    rw [hadj, hrev]
  have hzero : ∀ x ∈ X, P0' x = 0 := by
    intro x hx
    refine S.nondeg.2 _ (fun w => ?_)
    rw [← hadj]
    exact hiso _ (hX w) _ hx
  refine ⟨P0 - (θ : E) • (P0 ∘ₗ P0'), P0' - star (θ : E) • (P0 ∘ₗ P0'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    rw [hadj, hHH]
  · intro x hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hzero x hx, map_zero, smul_zero, sub_zero, hid x hx]
  · intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact X.sub_mem (hX y) (X.smul_mem _ (hHX y))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact Λ.sub_mem (hint l hl) (liso_smul_mem Λ θ (hint _ (hint' l hl)))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hbar]
    exact Λ.sub_mem (hint' l hl) (liso_smul_mem Λ (1 - θ) (hint _ (hint' l hl)))
  · intro w y
    have e1 : S.hT (P0' w) (P0' y) = S.hT w (P0 (P0' y)) := hrev _ _
    have e2 : S.hT (P0' w) (P0 (P0' y)) = S.hT w (P0 (P0' y)) := by
      rw [hrev, hid _ (hHX y)]
    have e3 : S.hT (P0 (P0' w)) (P0' y) = S.hT w (P0 (P0' y)) := by
      rw [← hadj, hid _ (hHX w), hHH]
    have e4 : S.hT (P0 (P0' w)) (P0 (P0' y)) = 0 := hiso _ (hHX w) _ (hHX y)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, star_star, RingHom.id_apply]
    rw [e1, e2, e3, e4]
    linear_combination (-(S.hT w (P0 (P0' y)))) * hθ

end Formalism.MainNotions.BridgeLemma

end
