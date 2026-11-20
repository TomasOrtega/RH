import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'`. Establish `hf : ∀ (γ : Γ) (x : Gf) (κ : K), ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ`. Introduce `γ x κ`. Rewrite using `[hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]`. Establish `hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1`.

Rewrite using `[Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]`. Establish `: (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[RCLike.conj_mul, hn]`. Simplify using the standard rewrite rules. Rewrite using `[this, one_mul]`.

Take `⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf)` from `⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩`. Establish `hbij : Function.Bijective g`. Prove the components needed by the constructor for the conclusion. Introduce `c1 c2 h`. Take `⟨γ1, κ1, h1⟩` from `hg c1`.

Take `⟨γ2, κ2, h2⟩` from `hg c2`. Rewrite `h1` using `[h]`. Use `(hs (s c2)).unique ?_ ⟨1, 1, by simp⟩` and prove the remaining obligations. Use `⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, h1]`.

Simplify using `only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Introduce `c'`. Take `⟨c, ⟨γ, κ, h⟩, -⟩` from `hs (s' c')`. Use `⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[h]`. Simplify using `only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Use `Fintype.sum_bijective g hbij _ _ (fun c => ?_)` and prove the remaining obligations. Take `⟨γ, κ, h⟩` from `hg c`.

Use `hf γ (s' (g c)) κ` as an intermediate fact. Rewrite `this` using `[← h]`. Conclude with `this`.
-/
theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
