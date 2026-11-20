import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

/- English proof (translation)
Introduce `I U hU`. Take `⟨g, hg, hsub⟩` from `I.topf_basis U (hU.mem_nhds U.one_mem)`. Conclude with `⟨g, hg, fun x hx => hsub hx⟩`.
-/
theorem stCong : StCong := by
  intro I U hU
  obtain ⟨g, hg, hsub⟩ := I.topf_basis U (hU.mem_nhds U.one_mem)
  exact ⟨g, hg, fun x hx => hsub hx⟩

/- English proof (translation)
Introduce `hC hK hG I U hU`. Take `⟨g, hg, hgU⟩` from `hC I U hU`. Take `⟨T, hT⟩` from `hK I g hg`. Take `⟨S, hS⟩` from `hG I`. Use `⟨(S ×ˢ T).image (fun p => p.1 * p.2), fun x => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, s, hs, k, hk, rfl⟩` from `hS x`. Take `⟨t, ht, u, hu, rfl⟩` from `hT k hk`. Use `⟨γ, hγ, s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, u, hgU hu, ?_⟩` and prove the remaining obligations. Simplify using `only [mul_assoc]`.
-/
theorem stTop : StTop := by
  intro hC hK hG I U hU
  classical
  obtain ⟨g, hg, hgU⟩ := hC I U hU
  obtain ⟨T, hT⟩ := hK I g hg
  obtain ⟨S, hS⟩ := hG I
  refine ⟨(S ×ˢ T).image (fun p => p.1 * p.2), fun x => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := hS x
  obtain ⟨t, ht, u, hu, rfl⟩ := hT k hk
  refine ⟨γ, hγ, s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, u, hgU hu, ?_⟩
  simp only [mul_assoc]

/- English proof (translation)
Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨w0, hw0, rfl⟩` from `(h v).1 hv`. Use `⟨(γ₀ : Matrix (Fin n) (Fin n) E) *ᵥ w0, (h₁ _).2 ⟨w0, hw0, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨w0, hw0, rfl⟩` from `(h₁ w).1 hw`. Use `(h _).2 ⟨w0, hw0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]`.
-/
theorem isImg_trans {E : Type} [Field E] [NumberField E] {n : ℕ} {γ γ₀ : GL (Fin n) E}
    {M₀ M₁ M : Submodule (𝓞 E) (Fin n → E)} (h₁ : IsImg γ₀ M₀ M₁) (h : IsImg γ M₀ M) :
    IsImg (γ * γ₀⁻¹) M₁ M := by
  intro v
  constructor
  · intro hv
    obtain ⟨w0, hw0, rfl⟩ := (h v).1 hv
    refine ⟨(γ₀ : Matrix (Fin n) (Fin n) E) *ᵥ w0, (h₁ _).2 ⟨w0, hw0, rfl⟩, ?_⟩
    rw [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w0, hw0, rfl⟩ := (h₁ w).1 hw
    refine (h _).2 ⟨w0, hw0, ?_⟩
    rw [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]

/- English proof (translation)
Introduce `hD hH I`. Take `⟨Λ, hΛ1, hΛ2, hΛ3⟩` from `hD I`. Take `⟨T, hT⟩` from `hH I.F I.E I.cm I.n I.J I.J_herm I.J_det`. Establish `huniq : ∀ {g : GL (Fin I.n) I.E} {A B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)}, IsImg g A B → IsImg g A B' → B = B'`. Introduce `g A B B' h h'`.

Use extensionality with `v`. Conclude with `(h v).trans (h' v).symm`. Set `rep : Submodule (𝓞 I.E) (Fin I.n → I.E) → I.Gf` to `fun M₀ => if h : ∃ y, Λ y = M₀ then Classical.choose h else 1`. Establish `hrep : ∀ M₀, (∃ y, Λ y = M₀) → Λ (rep M₀) = M₀`. Introduce `M₀ h`.

Use `show Λ (dite _ _ _) = M₀`. Rewrite using `[dif_pos h]`. Conclude with `Classical.choose_spec h`. Use `⟨T.image rep, fun x => ?_⟩` and prove the remaining obligations. Take `⟨hfg, hspan, hsd⟩` from `hΛ1 x`.

Take `⟨γ, hγ, M₀, hM₀, himg⟩` from `hT (Λ x) hfg hspan hsd`. Take `⟨c', -, -, hc'⟩` from `hΛ3 γ⁻¹ (Subgroup.inv_mem _ hγ)`. Establish `hrange : ∃ y, Λ y = M₀`. Use `⟨c' * x, ?_⟩` and prove the remaining obligations. Use extensionality with `v`.

Rewrite using `[hc' x v]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨w0, hw0, rfl⟩` from `(himg w).1 hw`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `hw0`. Introduce `hv`. Use `⟨(γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, (himg _).2 ⟨v, hv, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Take `⟨c, hcG, -, hc⟩` from `hΛ3 γ hγ`.

Establish `heq : Λ (c * rep M₀) = Λ x` using `huniq (hc (rep M₀)) (by rw [hrep M₀ hrange]; exact himg)`. Take `⟨k, hk, hxk⟩` from `hΛ2 _ _ heq`. Conclude with `⟨c, hcG, rep M₀, Finset.mem_image_of_mem _ hM₀, k, hk, hxk⟩`.
-/
theorem stGenusOf : StGenusOf := by
  intro hD hH I
  classical
  obtain ⟨Λ, hΛ1, hΛ2, hΛ3⟩ := hD I
  obtain ⟨T, hT⟩ := hH I.F I.E I.cm I.n I.J I.J_herm I.J_det
  have huniq : ∀ {g : GL (Fin I.n) I.E} {A B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)},
      IsImg g A B → IsImg g A B' → B = B' := by
    intro g A B B' h h'
    ext v
    exact (h v).trans (h' v).symm
  let rep : Submodule (𝓞 I.E) (Fin I.n → I.E) → I.Gf := fun M₀ =>
    if h : ∃ y, Λ y = M₀ then Classical.choose h else 1
  have hrep : ∀ M₀, (∃ y, Λ y = M₀) → Λ (rep M₀) = M₀ := by
    intro M₀ h
    show Λ (dite _ _ _) = M₀
    rw [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨T.image rep, fun x => ?_⟩
  obtain ⟨hfg, hspan, hsd⟩ := hΛ1 x
  obtain ⟨γ, hγ, M₀, hM₀, himg⟩ := hT (Λ x) hfg hspan hsd
  obtain ⟨c', -, -, hc'⟩ := hΛ3 γ⁻¹ (Subgroup.inv_mem _ hγ)
  have hrange : ∃ y, Λ y = M₀ := by
    refine ⟨c' * x, ?_⟩
    ext v
    rw [hc' x v]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w0, hw0, rfl⟩ := (himg w).1 hw
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hw0
    · intro hv
      refine ⟨(γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, (himg _).2 ⟨v, hv, rfl⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨c, hcG, -, hc⟩ := hΛ3 γ hγ
  have heq : Λ (c * rep M₀) = Λ x := huniq (hc (rep M₀)) (by rw [hrep M₀ hrange]; exact himg)
  obtain ⟨k, hk, hxk⟩ := hΛ2 _ _ heq
  exact ⟨c, hcG, rep M₀, Finset.mem_image_of_mem _ hM₀, k, hk, hxk⟩

end PIW.AdelClassFin
