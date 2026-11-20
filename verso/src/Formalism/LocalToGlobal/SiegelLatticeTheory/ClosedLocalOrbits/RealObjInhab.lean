import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open Matrix

namespace Formalism.L2.SG.RealObj

/- English proof (translation)
Unfold `Dl`. Rewrite using `[dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]`. Both sides reduce to the same expression.
-/
theorem Dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  unfold Dl
  rw [dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl

/- English proof (translation)
Establish `h2 : Dl (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) 2 = 2`. Rewrite using `[Dl_diagonal _ 2 le_rfl, Fin.prod_univ_two]`. Simplify using the standard rewrite rules. Establish `h1 : Dl (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) 1 = 1`. Rewrite using `[Dl_diagonal _ 1 (by norm_num), Fin.prod_univ_one]`.

Simplify using the standard rewrite rules. Unfold `Gv`. Rewrite using `[h2, h1]`. Evaluate the numerical expressions.
-/
theorem Gv_pos_example : 0 < Gv 1 1 (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) := by
  have h2 : Dl (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) 2 = 2 := by
    rw [Dl_diagonal _ 2 le_rfl, Fin.prod_univ_two]
    simp
  have h1 : Dl (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) 1 = 1 := by
    rw [Dl_diagonal _ 1 (by norm_num), Fin.prod_univ_one]
    simp
  unfold Gv
  rw [h2, h1]
  norm_num

/- English proof (translation)
Establish `h1 : Dl (Matrix.diagonal c) 1 = c 0`. Rewrite using `[Dl_diagonal _ 1 (by norm_num), Fin.prod_univ_one]`. Both sides reduce to the same expression. Unfold `JacV`. Rewrite using `[Finset.Icc_self, Finset.prod_singleton, h1]`.

Both sides reduce to the same expression.
-/
theorem JacV_diag_one (c : Fin 2 → ℂ) : JacV (Matrix.diagonal c) = (‖c 0‖ ^ 2) ^ 2 := by
  have h1 : Dl (Matrix.diagonal c) 1 = c 0 := by
    rw [Dl_diagonal _ 1 (by norm_num), Fin.prod_univ_one]
    rfl
  unfold JacV
  rw [Finset.Icc_self, Finset.prod_singleton, h1]
  rfl

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp [ZhatO]`.
-/
theorem ZhatO_signs (Z : Matrix (Fin 2) (Fin 2) ℂ) : ZhatO Z 0 0 = -Z 0 0 ∧ ZhatO Z 0 1 = Z 0 1 := by
  refine ⟨?_, ?_⟩ <;> simp [ZhatO]

/- English proof (translation)
Simplify using `[famSc, fam]`.
-/
theorem famSc_last {n r : ℕ} (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    famSc sc e z (Fin.last r) = z := by
  simp [famSc, fam]

/- English proof (translation)
Simplify using `only [trG, one_mul, mul_one]`.
-/
theorem trG_one {n : ℕ} {ε : Fin n → Bool} (γ : Formalism.REAL.UJ ε) :
    trG (1 : Matrix (Fin n) (Fin n) ℂ) 1 γ = Formalism.MainNotions.S.uMat γ := by
  simp only [trG, one_mul, mul_one]

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 2 1 [(1, 5), (2, 7)] = [(1, 5), (2, 7)] := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 [(1, 5), (1, 6), (2, 7)] = [(1, -5), (1, 6), (2, 7)] := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 (Formalism.L2.SG.DataInst.signAux 3 1 [(1, 5), (1, 6), (2, 7)]) =
    [(1, 5), (1, 6), (2, 7)] := by decide

end Formalism.L2.SG.RealObj
