import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjEntriesHasFDerivAtZero

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc3

noncomputable def pBLin {n : ℕ} (ε : Fin n → Bool) : (Mode ε → ℂ) →ₗ[ℝ] Mat n where
  toFun := pB ε
  map_add' B C := by
    funext a b
    simp only [pB, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp [star_add]
  map_smul' r B := by
    funext a b
    simp only [pB, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

/- English proof (translation)
Unfold `pB`. Rewrite using `[dif_pos x.2]`.
-/
theorem pB_mode {n : ℕ} (ε : Fin n → Bool) (B : Mode ε → ℂ) (x : Mode ε) :
    pB ε B x.1.1 x.1.2 = B x := by
  unfold pB
  rw [dif_pos x.2]

/- English proof (translation)
Introduce `n ε`. Take `⟨⟨L, hL, hD⟩, h2⟩` from `GlobalTheory.exp_conj_entries_hasFDerivAt_zero n (Mode ε) (pBLin ε) (fun x => x.1)`. Use `⟨?_, fun s => ?_⟩` and prove the remaining obligations. Establish `hLid : L = ContinuousLinearMap.id ℝ (Mode ε → ℂ)` using `by ext1 w; funext x`. Rewrite using `[hL]`.

Conclude with `pB_mode ε w x`. Rewrite using `[← hLid]`. Conclude with `hD`. Take `⟨L', hL', hD'⟩` from `h2 (Matrix.diagonal s)`. Use `⟨L', fun w x => ?_, hD'⟩` and prove the remaining obligations.

Rewrite using `[hL']`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal s * pB ε w - pB ε w * Matrix.diagonal s) x.1.1 x.1.2 = _`. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, pB_mode]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stExpDeriv : StExpDeriv := by
  intro n ε
  obtain ⟨⟨L, hL, hD⟩, h2⟩ :=
    GlobalTheory.exp_conj_entries_hasFDerivAt_zero n (Mode ε) (pBLin ε) (fun x => x.1)
  refine ⟨?_, fun s => ?_⟩
  · have hLid : L = ContinuousLinearMap.id ℝ (Mode ε → ℂ) := by
      ext1 w; funext x
      rw [hL]
      exact pB_mode ε w x
    rw [← hLid]
    exact hD
  · obtain ⟨L', hL', hD'⟩ := h2 (Matrix.diagonal s)
    refine ⟨L', fun w x => ?_, hD'⟩
    rw [hL']
    change (Matrix.diagonal s * pB ε w - pB ε w * Matrix.diagonal s) x.1.1 x.1.2 = _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, pB_mode]
    ring

end GlobalTheory.PsCo.Pc3
