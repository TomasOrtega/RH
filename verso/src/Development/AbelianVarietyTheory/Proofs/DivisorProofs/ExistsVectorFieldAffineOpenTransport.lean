import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

namespace GlobalTheory.FieldTransport

/- English proof (translation)
Introduce `Z W hW δ d' hd hδ`. Establish `hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O)` using `fun O h => hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])`. Set `e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O)` to `fun O h => haveI := hiso O h`. Use the proof step `(asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv`. Establish `he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f` using `fun _ _ _ => rfl`.

Establish `hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)), (hW.fromSpec.app O').hom (resG Z h f) = resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f)`. Introduce `O O' h f`. Use `congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)` as an intermediate fact. Simplify `this` using `[resG]`. Use `⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `O h f f'`. Simplify using `only [dif_pos h, map_add, hd.1 _ le_top]`. Introduce `O h f f'`. Simplify using `only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add, RingEquiv.symm_apply_apply]`. Introduce `O O' h hO f`.

Establish `hO' : O' ≤ W` using `h.trans hO`. Simplify using `only [dif_pos hO, dif_pos hO']`. Apply `(e O' hO').injective` to reduce the goal to its premises. Simplify using `only [RingEquiv.apply_symm_apply, he O' hO', hres]`. Rewrite using `[← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]`.

Conclude with `(e O' hO').apply_symm_apply _`. Introduce `a`. Simplify using `only [dif_pos (le_refl W)]`. Apply `(e W (le_refl W)).symm_apply_eq.mpr` to reduce the goal to its premises. Establish `hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤` using `le_top`.

Establish `key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x)`. Introduce `x`. Rewrite using `[he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]`. Both sides reduce to the same expression. Rewrite using `[key, key, hd.2.2 _ _ hs le_rfl, hδ]`.
-/
theorem exists_isField_transport : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  intro Z W hW δ d' hd hδ
  classical
  have hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O) := fun O h =>
    hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])
  let e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O) := fun O h =>
    haveI := hiso O h; (asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv
  have he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f := fun _ _ _ => rfl
  have hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)),
      (hW.fromSpec.app O').hom (resG Z h f) =
        resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f) := by
    intro O O' h f
    have := congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)
    simpa [resG] using this
  refine ⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro O h f f'
    simp only [dif_pos h, map_add, hd.1 _ le_top]
  · intro O h f f'
    simp only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add, RingEquiv.symm_apply_apply]
  · intro O O' h hO f
    have hO' : O' ≤ W := h.trans hO
    simp only [dif_pos hO, dif_pos hO']
    apply (e O' hO').injective
    simp only [RingEquiv.apply_symm_apply, he O' hO', hres]
    rw [← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]
    exact (e O' hO').apply_symm_apply _
  · intro a
    simp only [dif_pos (le_refl W)]
    apply (e W (le_refl W)).symm_apply_eq.mpr
    have hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤ := le_top
    have key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x) := by
      intro x
      rw [he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
      rfl
    rw [key, key, hd.2.2 _ _ hs le_rfl, hδ]

end GlobalTheory.FieldTransport
