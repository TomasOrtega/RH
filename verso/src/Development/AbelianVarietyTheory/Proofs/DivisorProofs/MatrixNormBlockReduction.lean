import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame

set_option autoImplicit false

namespace GlobalTheory.TriFrame

/- English proof (translation)
Unfold `matNorm`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨cf, h1, h2, h3, rfl⟩`.

Use `⟨cf ∘ Fin.succ, h1, fun k hk => h2 k.succ (Fin.succ_lt_succ_iff.2 hk), fun l => ?_, rfl⟩` and prove the remaining obligations. Use `h3 l.succ` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_succ, hcol l, mul_zero, zero_add]`. Simplify `this` using `[Matrix.submatrix_apply]`. Introduce and unpack `⟨cf', h1, h2, h3, rfl⟩`.

Use `⟨Fin.cons (-(∑ k, cf' k * N 0 k.succ) / N 0 0) cf', by simpa using h1, fun k hk => ?_, fun l => ?_, by simp⟩` and prove the remaining obligations. Consider the cases of `k using Fin.cases with`. Consider the case `zero => exact absurd hk (not_lt.2 (Fin.zero_le _))`. Consider the case `succ k => simpa using h2 k (Fin.succ_lt_succ_iff.1 hk)`. Consider the cases of `l using Fin.cases with`.

Consider the case `zero`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[div_mul_cancel₀ _ h0, neg_add_cancel, norm_zero]`. Conclude with `zero_le_one`.

Consider the case `succ l`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, hcol l, mul_zero, zero_add]`. Simplify `h3 l` using `[Matrix.submatrix_apply]`.
-/
theorem matNorm_succ_of_blockTri {C : Type} [NormedField C] {r : ℕ} (N : Matrix (Fin (r+1)) (Fin (r+1)) C)
    (h0 : N 0 0 ≠ 0) (hcol : ∀ l : Fin r, N l.succ 0 = 0) (i : Fin r) :
    matNorm N i.succ = matNorm (N.submatrix Fin.succ Fin.succ) i := by
  unfold matNorm
  congr 1
  ext t
  constructor
  · rintro ⟨cf, h1, h2, h3, rfl⟩
    refine ⟨cf ∘ Fin.succ, h1, fun k hk => h2 k.succ (Fin.succ_lt_succ_iff.2 hk), fun l => ?_, rfl⟩
    have := h3 l.succ
    rw [Fin.sum_univ_succ, hcol l, mul_zero, zero_add] at this
    simpa [Matrix.submatrix_apply] using this
  · rintro ⟨cf', h1, h2, h3, rfl⟩
    refine ⟨Fin.cons (-(∑ k, cf' k * N 0 k.succ) / N 0 0) cf', by simpa using h1, fun k hk => ?_, fun l => ?_, by simp⟩
    · cases k using Fin.cases with
      | zero => exact absurd hk (not_lt.2 (Fin.zero_le _))
      | succ k => simpa using h2 k (Fin.succ_lt_succ_iff.1 hk)
    · cases l using Fin.cases with
      | zero =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [div_mul_cancel₀ _ h0, neg_add_cancel, norm_zero]
        exact zero_le_one
      | succ l =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hcol l, mul_zero, zero_add]
        simpa [Matrix.submatrix_apply] using h3 l

end GlobalTheory.TriFrame
