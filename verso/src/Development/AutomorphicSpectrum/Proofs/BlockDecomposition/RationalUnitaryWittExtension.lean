import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

/- English proof (translation)
Establish `key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y)`. Introduce `x y`. Simplify using `only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Establish `hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i))`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (σ : E →+* E) M w i`. Rewrite using `[key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]`. Establish `: (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w`.

Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc]`. Establish `h` using `hM`. Unfold `cT at h`. Rewrite using `[h]`. Rewrite using `[this]`.
-/
theorem hE_mulVec_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J M : Matrix (Fin n) (Fin n) E) (hM : cT (σ : E →+* E) M * J * M = J) (w : Fin n → E) :
    hE σ J (M *ᵥ w) (M *ᵥ w) = hE σ J w w := by
  have key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) M w i
  rw [key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have : (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have h := hM
    unfold cT at h
    rw [h]
  rw [this]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n J _ γ hγ w`. Take `⟨M, hM, e⟩` from `hγ`. Use `⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩` and prove the remaining obligations. Establish `e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F` using `F) (AF F)) := by`. Use `congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e` as an intermediate fact.

Conclude with `this.symm`. Unfold `Sends`. Rewrite using `[e']`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm`.
-/
theorem exists_sends_hE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  intro F E _ _ _ _ _ σ _ n J _ γ hγ w
  obtain ⟨M, hM, e⟩ := hγ
  refine ⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩
  have e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    have := congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e
    exact this.symm
  unfold Sends
  rw [e']
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm

end GlobalTheory.CompanionTheory.RedCov

end
