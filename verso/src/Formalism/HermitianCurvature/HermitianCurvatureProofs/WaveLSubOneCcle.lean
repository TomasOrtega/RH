import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormExpMulISubOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLetterScal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨K1, hK1, hmul⟩` from `mult_phase (E := Wq →L[ℂ] Wp) m (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0))`. Use `⟨(K1 + 1) * 3 ^ w.length, by positivity, ?_⟩` and prove the remaining obligations. Introduce `σ hσ A x c hx e`. Establish `hc : 0 ≤ c` using `JCx2.pd_ccle_nonneg (hx e)`. Establish `hu` using `uInv_ccle (A + ((m + 1 : ℕ) : ℝ)) m σ hσ w x c hx e`.

Establish `h1` using `hmul σ hσ A (KB.uInv σ w x e) (3 ^ w.length * c) hu.1`. Establish `h2 : B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c)` using `BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hu.2`. Establish `h3` using `BetaSesquilinearity.CCle_add h1 h2`. Establish `hf : ((PBO.waveL Bs σ w - 1) x) e = fun g => (Complex.exp (PBFV.phaseL σ (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0)) g) - 1) • KB.uInv σ w x e g + (KB.uInv σ w x e g - x e g)`. Use function extensionality and compare the values at `g`.

Simplify using `only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, PBO.waveL, LinearMap.coe_mk, AddHom.coe_mk, KB.waveG]`. Rewrite using `[PBFV.fsv_dmin_one σ Bs.z Bs.z' g (by omega), sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hf]`. Use `JCx2.pd_ccle_mono_c h3 (le_of_eq ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem waveL_sub_one_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (((PBO.waveL Bs σ w - 1) x) e) (K * ‖σ‖ * c) := by
  obtain ⟨K1, hK1, hmul⟩ := mult_phase (E := Wq →L[ℂ] Wp) m
    (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0))
  refine ⟨(K1 + 1) * 3 ^ w.length, by positivity, ?_⟩
  intro σ hσ A x c hx e
  have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
  have hu := uInv_ccle (A + ((m + 1 : ℕ) : ℝ)) m σ hσ w x c hx e
  have h1 := hmul σ hσ A (KB.uInv σ w x e) (3 ^ w.length * c) hu.1
  have h2 : B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) :=
    BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hu.2
  have h3 := BetaSesquilinearity.CCle_add h1 h2
  have hf : ((PBO.waveL Bs σ w - 1) x) e = fun g =>
      (Complex.exp (PBFV.phaseL σ (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0)) g) - 1) •
        KB.uInv σ w x e g + (KB.uInv σ w x e g - x e g) := by
    funext g
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, PBO.waveL, LinearMap.coe_mk,
      AddHom.coe_mk, KB.waveG]
    rw [PBFV.fsv_dmin_one σ Bs.z Bs.z' g (by omega), sub_smul, one_smul]
    abel
  rw [hf]
  refine JCx2.pd_ccle_mono_c h3 (le_of_eq ?_)
  ring

/- English proof (translation)
Take `⟨K, hK, h1⟩` from `waveL_sub_one_ccle Bs w m`. Use `⟨K ^ 3, by positivity, ?_⟩` and prove the remaining obligations. Introduce `σ hσ A x c hx`. Use `set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM`. Establish `hx' : ∀ e, B.CCle ((A + M + M) + M) m (x e) c` using `fun e => by`.

Establish `: (A + M + M) + M = A + 3 * M` using `by ring`. Rewrite using `[this]`. Conclude with `hx e`. Establish `s1` using `h1 σ hσ (A + M + M) x c hx'`. Establish `s2` using `h1 σ hσ (A + M) _ _ s1`.

Establish `s3` using `h1 σ hσ A _ _ s2`. Introduce `e`. Establish `he : PBO.mDiff Bs σ w x = (PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) x))`. Simplify using `only [PBO.mDiff, pow_succ, pow_zero, one_mul]`. Both sides reduce to the same expression.

Rewrite using `[he]`. Use `JCx2.pd_ccle_mono_c (s3 e) (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mDiff_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m ((PBO.mDiff Bs σ w x) e) (K * ‖σ‖ ^ 3 * c) := by
  obtain ⟨K, hK, h1⟩ := waveL_sub_one_ccle Bs w m
  refine ⟨K ^ 3, by positivity, ?_⟩
  intro σ hσ A x c hx
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM
  have hx' : ∀ e, B.CCle ((A + M + M) + M) m (x e) c := fun e => by
    have : (A + M + M) + M = A + 3 * M := by ring
    rw [this]; exact hx e
  have s1 := h1 σ hσ (A + M + M) x c hx'
  have s2 := h1 σ hσ (A + M) _ _ s1
  have s3 := h1 σ hσ A _ _ s2
  intro e
  have he : PBO.mDiff Bs σ w x = (PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) x)) := by
    simp only [PBO.mDiff, pow_succ, pow_zero, one_mul]
    rfl
  rw [he]
  refine JCx2.pd_ccle_mono_c (s3 e) (le_of_eq ?_)
  ring

end one

end Formalism.FourierDecayAlt.P.StandardPairingDecay
