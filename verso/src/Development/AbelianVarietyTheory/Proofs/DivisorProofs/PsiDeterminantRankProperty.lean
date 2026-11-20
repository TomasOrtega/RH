import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTiltAutomorphismTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiMuAssociatedOfPrimitiveRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantOrdersIndependentOfRootStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ γ hγ N Δ a c hΔ hord`. Take `⟨γC, hγC, hvγ⟩` from `hγ`. Take `⟨Γ, ε', hε', hξ, hμ, hψΓ, hθ⟩` from `GlobalTheory.T.exists_tilt_automorphism_transport p O ε Λ ψ γ.symm hψ hε`. Establish `halg : ∀ x : O, algebraMap O C (γ.symm x) = γC.symm (algebraMap O C x)`. Introduce `x`.

Apply `γC.injective` to reduce the goal to its premises. Rewrite using `[hγC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Establish `huniq : ∀ (σ : Λ →+* O) (f g : RL p O Λ →+* O), IsTheta σ f → IsTheta σ g → f = g`. Introduce `σ f g hf hg`. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => rw [hf, hg]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hcomp : ∀ σ : Λ →+* O, ((γ.symm : O ≃+* O) : O →+* O).comp ((γ : O →+* O).comp σ) = σ`. Introduce `σ`. Use extensionality with `l`. Simplify using the standard rewrite rules. Establish `hkey : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f₁ : RL p O Λ →+* O, IsTheta ((γ : O →+* O).comp σ) f₁ ∧ ∀ r, f (Γ r) = γ.symm (f₁ r)`.

Introduce `σ f hf`. Take `⟨f₁, hf₁, -⟩` from `theta_tensor_exists p C v O hv ε hε Λ ((γ : O →+* O).comp σ)`. Take `⟨f'', hf'', hf''Γ⟩` from `hθ _ f₁ hf₁`. Rewrite `hf''` using `[hcomp]`. Establish `he` using `huniq σ f'' f hf'' hf`.

Conclude with `⟨f₁, hf₁, fun r => by rw [← he]; exact hf''Γ r⟩`. Establish `hΔ' : IsDetElt ε' ψ N (Γ Δ)`. Take `⟨hdiv, g, hg, hgdiv⟩` from `hΔ`. Use `⟨?_, Γ g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hμ, ← map_pow]`.

Conclude with `map_dvd Γ hdiv`. Rewrite using `[← hψΓ, ← map_mul, ← hg]`. Rewrite using `[← hξ, ← map_pow]`. Conclude with `map_dvd Γ hgdiv`. Establish `hord' : HasOrders C ε' N (Γ Δ) (fun σ => a ((γ : O →+* O).comp σ)) (fun σ => γC.symm (c ((γ : O →+* O).comp σ)))`.

Introduce `σ f hf`. Take `⟨f₁, hf₁, hfΓ⟩` from `hkey σ f hf`. Take `⟨hle, hc, s, t, hs, hst, ht⟩` from `hord _ f₁ hf₁`. Use `⟨hle, (map_ne_zero γC.symm).mpr hc, Γ s, Γ t, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply] at hs ⊢`.

Rewrite using `[hfΓ, halg]`. Conclude with `(map_ne_zero γC.symm).mpr hs`. Rewrite using `[← map_mul, hst, map_mul, map_pow, hξ]`. Simplify using `only [RingHom.comp_apply] at ht ⊢`. Rewrite using `[hfΓ, hfΓ, halg, halg, ht, map_mul]`.

Take `⟨hxi, hmu⟩` from `GlobalTheory.T.xi_mu_associated_of_primitive_roots p C v O hv ε' hε' ε hε`. Take `⟨c', h1, h2, h3⟩` from `GlobalTheory.T.determinant_orders_independent_of_root p C v O hv ε' ε Λ ψ N (Γ Δ) _ _ hxi hmu hΔ' hord'`. Use `⟨Γ Δ, c', h1, h2, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[h3, ← hvγ (γC.symm _), RingEquiv.apply_symm_apply]`.
-/
theorem detElt_transport_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ (Δ' : RL p O Λ) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ' ∧ HasOrders C ε N Δ' (fun σ => a ((γ : O →+* O).comp σ)) c' ∧ ∀ σ, v (c' σ) = v (c ((γ : O →+* O).comp σ)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ γ hγ N Δ a c hΔ hord
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  obtain ⟨Γ, ε', hε', hξ, hμ, hψΓ, hθ⟩ := GlobalTheory.T.exists_tilt_automorphism_transport p O ε Λ ψ γ.symm hψ hε
  have halg : ∀ x : O, algebraMap O C (γ.symm x) = γC.symm (algebraMap O C x) := by
    intro x
    apply γC.injective
    rw [hγC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have huniq : ∀ (σ : Λ →+* O) (f g : RL p O Λ →+* O), IsTheta σ f → IsTheta σ g → f = g := by
    intro σ f g hf hg
    apply RingHom.ext
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hf, hg]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomp : ∀ σ : Λ →+* O, ((γ.symm : O ≃+* O) : O →+* O).comp ((γ : O →+* O).comp σ) = σ := by
    intro σ
    ext l
    simp
  have hkey : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f →
      ∃ f₁ : RL p O Λ →+* O, IsTheta ((γ : O →+* O).comp σ) f₁ ∧ ∀ r, f (Γ r) = γ.symm (f₁ r) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, -⟩ := theta_tensor_exists p C v O hv ε hε Λ ((γ : O →+* O).comp σ)
    obtain ⟨f'', hf'', hf''Γ⟩ := hθ _ f₁ hf₁
    rw [hcomp] at hf''
    have he := huniq σ f'' f hf'' hf
    exact ⟨f₁, hf₁, fun r => by rw [← he]; exact hf''Γ r⟩
  have hΔ' : IsDetElt ε' ψ N (Γ Δ) := by
    obtain ⟨hdiv, g, hg, hgdiv⟩ := hΔ
    refine ⟨?_, Γ g, ?_, ?_⟩
    · rw [← hμ, ← map_pow]; exact map_dvd Γ hdiv
    · rw [← hψΓ, ← map_mul, ← hg]
    · rw [← hξ, ← map_pow]; exact map_dvd Γ hgdiv
  have hord' : HasOrders C ε' N (Γ Δ) (fun σ => a ((γ : O →+* O).comp σ))
      (fun σ => γC.symm (c ((γ : O →+* O).comp σ))) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, hfΓ⟩ := hkey σ f hf
    obtain ⟨hle, hc, s, t, hs, hst, ht⟩ := hord _ f₁ hf₁
    refine ⟨hle, (map_ne_zero γC.symm).mpr hc, Γ s, Γ t, ?_, ?_, ?_⟩
    · simp only [RingHom.comp_apply] at hs ⊢
      rw [hfΓ, halg]
      exact (map_ne_zero γC.symm).mpr hs
    · rw [← map_mul, hst, map_mul, map_pow, hξ]
    · simp only [RingHom.comp_apply] at ht ⊢
      rw [hfΓ, hfΓ, halg, halg, ht, map_mul]
  obtain ⟨hxi, hmu⟩ := GlobalTheory.T.xi_mu_associated_of_primitive_roots p C v O hv ε' hε' ε hε
  obtain ⟨c', h1, h2, h3⟩ := GlobalTheory.T.determinant_orders_independent_of_root p C v O hv ε' ε Λ ψ N (Γ Δ) _ _ hxi hmu hΔ' hord'
  refine ⟨Γ Δ, c', h1, h2, fun σ => ?_⟩
  rw [h3, ← hvγ (γC.symm _), RingEquiv.apply_symm_apply]

end GlobalTheory.DetInv
