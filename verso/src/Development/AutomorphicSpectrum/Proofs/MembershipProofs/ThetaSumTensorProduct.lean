import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularityStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SeesawThetaDualPairStatement

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ThetaMember

section General

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β : Type} [Fintype β] [DecidableEq β]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro (i | i) (j | j) <;> simp [dbl, h.1]`. Rewrite using `[dbl, det_fromBlocks_zero₂₁, det_neg]`. Conclude with `h.2.mul ((isUnit_one.neg.pow _).mul h.2)`.
-/
theorem isHerm_dbl {J : Matrix β β E} (h : IsHerm c J) : IsHerm c (dbl J) := by
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> simp [dbl, h.1]
  · rw [dbl, det_fromBlocks_zero₂₁, det_neg]
    exact h.2.mul ((isUnit_one.neg.pow _).mul h.2)

/- English proof (translation)
Establish `hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J` using `g.2`. Use `⟨⟨⟨fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1, fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[fromBlocks_multiply, Units.mul_inv]`. Simplify using the standard rewrite rules. Rewrite using `[fromBlocks_multiply, Units.inv_mul]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J * (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J`. Rewrite using `[fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply, Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]`. Simplify using `[hg]`.
-/
theorem exists_dbl_elem {J : Matrix β β E} (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  refine ⟨⟨⟨fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [fromBlocks_multiply, Units.mul_inv]; simp
  · rw [fromBlocks_multiply, Units.inv_mul]; simp
  · change (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
      (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply,
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]
    simp [hg]

end General

def dblCoord {F : Type} [Field F] {E : Type} [AddCommGroup E] [Module F E] {α β κ : Type}
    (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F)) :
    Matrix α (β ⊕ β) E ≃ₗ[F] (κ ⊕ κ → F) × (κ ⊕ κ → F) where
  toFun x := (Sum.elim (d₀ x.toCols₁).1 (d₀ x.toCols₂).1, Sum.elim (d₀ x.toCols₁).2 (-(d₀ x.toCols₂).2))
  invFun p := fromCols (d₀.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl)) (d₀.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
  map_add' x y := by
    have h1 : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
    have h2 : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
    rw [h1, h2, map_add, map_add]
    ext (i | i) <;> simp [add_comm]
  map_smul' a x := by
    have h1 : (a • x).toCols₁ = a • x.toCols₁ := rfl
    have h2 : (a • x).toCols₂ = a • x.toCols₂ := rfl
    rw [h1, h2, map_smul, map_smul]
    ext (i | i) <;> simp
  left_inv x := by
    simp
  right_inv p := by
    simp only [toCols₁_fromCols, toCols₂_fromCols, LinearEquiv.apply_symm_apply]
    ext (i | i) <;> simp

/- English proof (translation)
Substitute `hJ hC` using the available equality. Conclude with `GlobalTheory.T.weil_representation_theta_equivariance F E c ξ α β κ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ ν Cy om hχ hL hS hR g hg`.
-/
theorem split_of_eq (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (h1 : Continuous ψ) (h2 : ψ ≠ 1) (h3 : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    (hq : IsQuad c ξ) (hA : IsHerm c JA) (hB : IsHerm c JB)
    (J' : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) (hJ : JB.map (fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = J')
    (d : Darboux (symp (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) J') κ)
    (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F))
    (hd : ∀ x, d.e (x.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) =
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).2 i)))
    (χ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle) (ν : Type) [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E)
    (C' : Matrix β ν (AdeleRing (𝓞 F) F ⊗[F] E)) (hC : Cy.map (fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = C')
    (om : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) J' →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (hχ : ∀ (z : E) (u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), (u : AdeleRing (𝓞 F) F ⊗[F] E) = (1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z → χ u = 1)
    (hL : IsLagr c JB Cy) (hS : IsSplitting (adeleClass F) ψ d (actB (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c)) om)
    (hR : SiegelRule (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (adeleClass F) ψ ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) J' d χ C' om)
    (g : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) J')
    (hg : ∃ γ : Matrix β β E, ((g : GL β (AdeleRing (𝓞 F) F ⊗[F] E)) : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) = γ.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  subst hJ hC
  exact GlobalTheory.T.weil_representation_theta_equivariance F E c ξ α β κ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ ν Cy om hχ hL hS hR g hg

/- English proof (translation)
Introduce `F _ _ _ _ E _ _ c ξ α β κ _ _ _ _ _ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ om hχ hW g hg Φ hΦ`. Take `⟨hS, dd, omd, hdd, hSd, hRd, hbox⟩` from `hW`. Take `⟨γ, hγ⟩` from `hg`. Take `⟨gd, hgd⟩` from `exists_dbl_elem g`. Take `⟨-, -, Φ₀, hΦ₀, hne⟩` from `GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ`.

Establish `: Invertible (2 : F)` using `invertibleOfNonzero two_ne_zero`. Establish `key` using `split_of_eq F E c ξ α (β ⊕ β) (κ ⊕ κ) JA (dbl JB) ψ h1 h2 h3 hq hA (isHerm_dbl hB) _ ?_ dd (dblCoord d₀) ?_ χ β (diagCols β) _ ?_ omd hχ (isLagr_diagCols c JB) hSd hRd gd ⟨fromBlocks γ 0 0 1, ?_⟩ (boxFun Φ Φ₀) (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ Φ₀ hΦ₀).1`. Rewrite `key` using `[hbox g gd hgd Φ hΦ Φ₀ hΦ₀, (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (hS.pres g Φ hΦ) Φ₀ hΦ₀).2, (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ Φ₀ hΦ₀).2]`. Conclude with `mul_right_cancel₀ hne key`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [dbl, TensorProduct.tmul_neg]`.

Introduce `x`. Rewrite using `[← fromCols_toCols x, fromCols_map, hdd, hd, hd]`. Apply the tactic sequence `ext (i | i) <;> simp [dblCoord]`. Apply the tactic sequence `ext (i | i) j <;> by_cases h : i = j <;> simp [diagCols, h, Matrix.one_apply, Algebra.TensorProduct.one_def]`. Rewrite using `[hgd, hγ]`.

Use extensionality with `(i | i) (j | j)`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply, Algebra.TensorProduct.one_def]`.
-/
theorem theta_om_rational : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → IsQuad c ξ → IsHerm c JA → IsHerm c JB → ∀ (d : Darboux (symp (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E))) κ) (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F)), (∀ x, d.e (x.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).2 i))) → ∀ (χ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle) (om : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)), (∀ (z : E) (u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), (u : AdeleRing (𝓞 F) F ⊗[F] E) = (1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z → χ u = 1) → IsWeilB (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (adeleClass F) ψ ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) d χ om → ∀ g : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)), (∃ γ : Matrix β β E, ((g : GL β (AdeleRing (𝓞 F) F ⊗[F] E)) : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) = γ.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) → ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  intro F _ _ _ _ E _ _ c ξ α β κ _ _ _ _ _ JA JB ψ h1 h2 h3 hq hA hB d d₀ hd χ om hχ hW g hg Φ hΦ
  obtain ⟨hS, dd, omd, hdd, hSd, hRd, hbox⟩ := hW
  obtain ⟨γ, hγ⟩ := hg
  obtain ⟨gd, hgd⟩ := exists_dbl_elem g
  obtain ⟨-, -, Φ₀, hΦ₀, hne⟩ := GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have key := split_of_eq F E c ξ α (β ⊕ β) (κ ⊕ κ) JA (dbl JB) ψ h1 h2 h3 hq hA (isHerm_dbl hB) _ ?_ dd
    (dblCoord d₀) ?_ χ β (diagCols β) _ ?_ omd hχ (isLagr_diagCols c JB) hSd hRd gd ⟨fromBlocks γ 0 0 1, ?_⟩
    (boxFun Φ Φ₀) (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ Φ₀ hΦ₀).1
  · rw [hbox g gd hgd Φ hΦ Φ₀ hΦ₀, (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (hS.pres g Φ hΦ) Φ₀ hΦ₀).2,
      (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ Φ₀ hΦ₀).2] at key
    exact mul_right_cancel₀ hne key
  · ext (i | i) (j | j) <;> simp [dbl, TensorProduct.tmul_neg]
  · intro x
    rw [← fromCols_toCols x, fromCols_map, hdd, hd, hd]
    ext (i | i) <;> simp [dblCoord]
  · ext (i | i) j <;> by_cases h : i = j <;> simp [diagCols, h, Matrix.one_apply, Algebra.TensorProduct.one_def]
  · rw [hgd, hγ]
    ext (i | i) (j | j)
    · simp
    · simp
    · simp
    · by_cases h : i = j <;> simp [h, Matrix.one_apply, Algebra.TensorProduct.one_def]

end GlobalTheory.CompanionTheory.ThetaMember
