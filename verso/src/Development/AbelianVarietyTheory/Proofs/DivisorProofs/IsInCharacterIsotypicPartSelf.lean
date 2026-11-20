import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix', Matrix.trace]`. Simplify using `[LinearMap.toMatrix'_apply]`.
-/
theorem trace_pi_eq_sum (n : ℕ) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.trace ℂ (Fin n → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

/- English proof (translation)
Introduce `G _ _ Y hY V _ _ _ ρ h`. Establish `: Fintype G` using `Fintype.ofFinite G`. Take `⟨n, σ, hσ⟩` from `hY`. Establish `hYc : ∀ g, Y g = σ.character g` using `fun g => by simpa using hσ g`. Establish `hst : ∀ g, star (Y g) = σ.character g⁻¹` using `fun g => by`.

Rewrite using `[star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]`. Rewrite `h` using `[finsum_eq_sum_of_fintype]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [hst] at h ⊢`. Establish `hinv : Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (by`.

Establish `: 0 < Nat.card G` using `Nat.card_pos`. Conclude with `this.ne')` after adjusting the coercions. Establish `hfr` using `Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)`. Simplify using `only [Representation.char_linHom] at hfr`. Establish `h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0` using `h`.

Rewrite `hfr` using `[h', mul_zero]`. Establish `hbot : (Representation.linHom σ ρ).invariants = ⊥`. Apply `Submodule.finrank_eq_zero.mp` to reduce the goal to its premises. Conclude with `hfr.symm` after adjusting the coercions. Establish `hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0`.

Introduce `f`. Establish `hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants`. Introduce `h`. Rewrite using `[map_sum]`. Simplify using `only [← Module.End.mul_apply, ← map_mul]`.

Conclude with `Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)`. Rewrite `hm` using `[hbot]`. Conclude with `(Submodule.mem_bot ℂ).mp hm`. Use extensionality with `v`. Establish `key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0`.

Introduce `i`. Use `congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1)) (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))` as an intermediate fact. Simplify `this` using `[Representation.linHom_apply, LinearMap.sum_apply]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]`. Simplify using `only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero (fun i _ => key i)`.
-/
theorem kills_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  intro G _ _ Y hY V _ _ _ ρ h
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h
  rw [finsum_eq_sum_of_fintype]
  simp only [hst] at h ⊢

  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  have h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at hfr
  have hbot : (Representation.linHom σ ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm

  have hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants := by
      intro h
      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin
