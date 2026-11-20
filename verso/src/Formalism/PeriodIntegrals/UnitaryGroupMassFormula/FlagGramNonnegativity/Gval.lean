import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.HasSignatureExistsNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.ConjTMulMulApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.BinaryFormMulEqNormSqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.NatAddZeroFinOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.SumMulCommMulVec

noncomputable section

open Matrix PI.FlagGramNonneg ComplexConjugate

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

/- English proof (translation)
Unfold `PI.FlagGramNonneg`. Introduce `E _ _ _ V _ _ _ hT hS hN N b τ hτ p r T T' hsig hT0 hT'0 e e' z z' hf hf'`. Take `⟨-, he, hez, hzz⟩` from `hf`. Take `⟨-, he', hez', hzz'⟩` from `hf'`. Establish `hsym : ∀ x y, hT y x = star (hT x y)` using `fun x y => by`.

Rewrite using `[← hS.eq x y, starRingEnd_apply]`. Use `set Z := zhat hT (fvec e z) (fvec e' z') with hZ`. Establish `hsub : Z.submatrix Fin.castSucc Fin.castSucc = amat hT e e'`. Use extensionality with `a c`. Simplify using `[hZ, zhat, fvec, amat]`.

Establish `hg : gval Z (T : E) (T' : E) = Z.det * star Z.det - (T : E) * T' * ((amat hT e e').det * star (amat hT e e').det)`. Rewrite using `[gval, leadMinorE_succ, leadMinorE_self, hsub]`. Distinguish the cases in `hA : IsUnit (amat hT e e').det`. Establish `hsubU : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det`. Rewrite using `[hsub]`.

Conclude with `hA`. Establish `hrow : (fun c => Z (Fin.last r) (Fin.castSucc c)) = vvec hT z e'`. Use function extensionality and compare the values at `c`. Simplify using `[hZ, zhat, fvec, vvec]`. Establish `hcol : (fun a => Z (Fin.castSucc a) (Fin.last r)) = uvec hT e z'`.

Use function extensionality and compare the values at `a`. Simplify using `[hZ, zhat, fvec, uvec]`. Establish `hll : Z (Fin.last r) (Fin.last r) = hT z z'`. Simplify using `[hZ, zhat, fvec]`. Establish `hdet : Z.det = (amat hT e e').det * sval hT e e' z z'`.

Rewrite using `[det_succ_schur Z hsubU, hsub, hll, hrow, hcol]`. Both sides reduce to the same expression. Establish `hs : (T : ℝ) * T' ≤ Complex.normSq (τ (sval hT e e' z z'))`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Use `set y : Fin r ⊕ Fin 2 → V := Sum.elim (yv hT e e') ![zt hT e e' z, zt' hT e e' z'] with hy`. Establish `hyz : ∀ a, hT (zt hT e e' z) (yv hT e e' a) = 0` using `fun a => by`. Rewrite using `[hsym, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez) (a := a), star_zero]`. Establish `hyz' : ∀ a, hT (zt' hT e e' z') (yv hT e e' a) = 0` using `fun a => by`. Rewrite using `[hsym, yv_zt' (hA := hA) (he' := he') (hez' := hez') (a := a), star_zero]`.

Establish `hz'z : hT (zt' hT e e' z') (zt hT e e' z) = star (sval hT e e' z z')`. Rewrite using `[hsym, zt_zt' (hA := hA)]`. Establish `hG : (Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((gram hT b).map τ) * (Matrix.of fun n k => τ (b.repr (y k) n)) = gamma r T T' (τ (sval hT e e' z z'))`. Use extensionality with `i j`. Rewrite using `[gram_tau hT b τ hτ y i j]`.

Apply the tactic sequence `rcases i with a | i <;> rcases j with c | j`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Simplify using `[hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), map_ofNat]`. Simplify using `[hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), hac]`.

Apply the tactic sequence `fin_cases j <;> simp [hy, gamma, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez), yv_zt' (hA := hA) (he' := he') (hez' := hez')]`. Apply the tactic sequence `fin_cases i <;> simp [hy, gamma, hyz, hyz']`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[hy, gamma, zt_zt (hS := hS) (he := he) (hez := hez), zt'_zt' (hS := hS) (he' := he') (hez' := hez'), zt_zt' (hA := hA), hz'z, hzz, hzz', hτ]`. Establish `hcard : r + 1 < Fintype.card (Fin r ⊕ Fin 2)`.

Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc0, hcnn⟩` from `hasSignature_exists_nonneg _ hsig hcard (Matrix.of fun n k => τ (b.repr (y k) n))`. Rewrite `hcnn` using `[form_mulVec, hG]`. Establish `hneg` using `gamma_neg r T T' (by exact_mod_cast hT0) (by exact_mod_cast hT'0) _ hlt c hc0`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨Complex.normSq (τ (amat hT e e').det) * (Complex.normSq (τ (sval hT e e' z z')) - T * T'), mul_nonneg (Complex.normSq_nonneg _) (by linarith), ?_⟩` and prove the remaining obligations. Rewrite using `[hg, hdet]`. Simplify using `only [map_sub, map_mul, star_mul', hτ, map_natCast]`. Use `push_cast`.

Rewrite using `[← Complex.mul_conj, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (amat hT e e').det = 0`. Assume the negation of the conclusion as `h`. Conclude with `hA (isUnit_iff_ne_zero.mpr h)`.

Use `⟨Complex.normSq (τ Z.det), Complex.normSq_nonneg _, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, h0]`. Simplify using `[hτ, Complex.mul_conj]`.
-/
theorem main : PI.FlagGramNonneg := by
  unfold PI.FlagGramNonneg
  intro E _ _ _ V _ _ _ hT hS hN N b τ hτ p r T T' hsig hT0 hT'0 e e' z z' hf hf'
  obtain ⟨-, he, hez, hzz⟩ := hf
  obtain ⟨-, he', hez', hzz'⟩ := hf'
  have hsym : ∀ x y, hT y x = star (hT x y) := fun x y => by
    rw [← hS.eq x y, starRingEnd_apply]
  set Z := zhat hT (fvec e z) (fvec e' z') with hZ
  have hsub : Z.submatrix Fin.castSucc Fin.castSucc = amat hT e e' := by
    ext a c
    simp [hZ, zhat, fvec, amat]
  have hg : gval Z (T : E) (T' : E) = Z.det * star Z.det -
      (T : E) * T' * ((amat hT e e').det * star (amat hT e e').det) := by
    rw [gval, leadMinorE_succ, leadMinorE_self, hsub]
  by_cases hA : IsUnit (amat hT e e').det
  ·
    have hsubU : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [hsub]; exact hA
    have hrow : (fun c => Z (Fin.last r) (Fin.castSucc c)) = vvec hT z e' := by
      funext c; simp [hZ, zhat, fvec, vvec]
    have hcol : (fun a => Z (Fin.castSucc a) (Fin.last r)) = uvec hT e z' := by
      funext a; simp [hZ, zhat, fvec, uvec]
    have hll : Z (Fin.last r) (Fin.last r) = hT z z' := by
      simp [hZ, zhat, fvec]
    have hdet : Z.det = (amat hT e e').det * sval hT e e' z z' := by
      rw [det_succ_schur Z hsubU, hsub, hll, hrow, hcol]
      rfl

    have hs : (T : ℝ) * T' ≤ Complex.normSq (τ (sval hT e e' z z')) := by
      by_contra hlt
      push_neg at hlt
      set y : Fin r ⊕ Fin 2 → V :=
        Sum.elim (yv hT e e') ![zt hT e e' z, zt' hT e e' z'] with hy
      have hyz : ∀ a, hT (zt hT e e' z) (yv hT e e' a) = 0 := fun a => by
        rw [hsym, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez) (a := a), star_zero]
      have hyz' : ∀ a, hT (zt' hT e e' z') (yv hT e e' a) = 0 := fun a => by
        rw [hsym, yv_zt' (hA := hA) (he' := he') (hez' := hez') (a := a), star_zero]
      have hz'z : hT (zt' hT e e' z') (zt hT e e' z) = star (sval hT e e' z z') := by
        rw [hsym, zt_zt' (hA := hA)]
      have hG : (Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((gram hT b).map τ) *
          (Matrix.of fun n k => τ (b.repr (y k) n)) =
          gamma r T T' (τ (sval hT e e' z z')) := by
        ext i j
        rw [gram_tau hT b τ hτ y i j]
        rcases i with a | i <;> rcases j with c | j
        · by_cases hac : a = c
          · subst hac
            simp [hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), map_ofNat]
          · simp [hy, gamma, yv_yv (hS := hS) (hA := hA) (he := he) (he' := he'), hac]
        · fin_cases j <;> simp [hy, gamma, yv_zt (hS := hS) (hA := hA) (he := he) (hez := hez), yv_zt' (hA := hA) (he' := he') (hez' := hez')]
        · fin_cases i <;> simp [hy, gamma, hyz, hyz']
        · fin_cases i <;> fin_cases j <;>
            simp [hy, gamma, zt_zt (hS := hS) (he := he) (hez := hez), zt'_zt' (hS := hS) (he' := he') (hez' := hez'), zt_zt' (hA := hA), hz'z, hzz, hzz', hτ]
      have hcard : r + 1 < Fintype.card (Fin r ⊕ Fin 2) := by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega
      obtain ⟨c, hc0, hcnn⟩ := hasSignature_exists_nonneg _ hsig hcard
        (Matrix.of fun n k => τ (b.repr (y k) n))
      rw [form_mulVec, hG] at hcnn
      have hneg := gamma_neg r T T' (by exact_mod_cast hT0) (by exact_mod_cast hT'0) _ hlt c hc0
      linarith
    refine ⟨Complex.normSq (τ (amat hT e e').det) *
      (Complex.normSq (τ (sval hT e e' z z')) - T * T'),
      mul_nonneg (Complex.normSq_nonneg _) (by linarith), ?_⟩
    rw [hg, hdet]
    simp only [map_sub, map_mul, star_mul', hτ, map_natCast]
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    ring
  ·
    have h0 : (amat hT e e').det = 0 := by
      by_contra h
      exact hA (isUnit_iff_ne_zero.mpr h)
    refine ⟨Complex.normSq (τ Z.det), Complex.normSq_nonneg _, ?_⟩
    rw [hg, h0]
    simp [hτ, Complex.mul_conj]

end PI.UnitaryGroupMassFormula.FlagGramNonneg
