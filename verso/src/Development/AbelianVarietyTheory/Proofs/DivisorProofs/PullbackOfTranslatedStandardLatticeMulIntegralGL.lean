import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

/- English proof (translation)
Take `⟨k0, rfl⟩` from `hk`. Conclude with `(k0.val i j).2`.
-/
theorem entry_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) (i j : Fin n) : (k : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨k0, rfl⟩ := hk
  exact (k0.val i j).2

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)`.
-/
theorem mulVec_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) {v : Fin n → L} (hv : ∀ i, v i ∈ O) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) L) *ᵥ v) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)

/- English proof (translation)
Introduce `E _ _ _ w K B n ψ g k hk`. Establish `hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w n` using `inv_mem hk`. Use extensionality with `y`. Use `show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔ (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)`. Simplify using `only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]`.

Prove the components needed by the constructor for the conclusion. Introduce `h c i`. Establish `e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) = (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)))`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[e]`.

Conclude with `mulVec_mem_of_mem_GLint hk (fun j => h c j) i`. Introduce `h c i`. Conclude with `mulVec_mem_of_mem_GLint hk' (fun j => h c j) i`.
-/
theorem pullLat_mul_of_mem_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  intro E _ _ _ w K B n ψ g k hk
  have hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w n := inv_mem hk
  ext y
  show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
    (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)
  simp only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro h c i
    have e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) =
        (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y))) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_of_mem_GLint hk (fun j => h c j) i
  · intro h c i
    exact mulVec_mem_of_mem_GLint hk' (fun j => h c j) i

end GlobalTheory.KapOrb
