import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.VecMulScCInr

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA5

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E}

/- English proof (translation)
Unfold `dlast`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `split_ifs`.

Conclude with `h.αn`. Conclude with `mul_one 1`.
-/
theorem dlast_mul_cj (h : ScHyp O cj qi T T' α) : dlast r α * dlast r (cj α) = 1 := by
  unfold dlast
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · exact h.αn
  · exact mul_one 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scPhi_symm_apply (h : ScHyp O cj qi T T' α) (Y : Ix r → O) :
    (scPhi (r := r) h).symm Y = Matrix.vecMul Y (scA' h) := rfl

/- English proof (translation)
Establish `hG` using `gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh`. Establish `hG' : gramG cj qi Zh T T' = (scC r (cj α) (-((α - 1) * qi * cj α))).transpose * gramG cj qi (Zh * dlast r α) T T' * (scC r (cj α) (-((α - 1) * qi * cj α))).map cj`. Use `gramG_scale cj qi h.cjcj (cj α) T T' (by rw [h.cjcj, mul_comm]; exact h.αn) h.qic h.Tc h.T'c (Zh * dlast r α)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, dlast_mul_cj h, Matrix.mul_one]`. Establish `hb : (cj α - 1) * qi = -((α - 1) * qi * cj α)` using `by linear_combination qi * h.αn`.

Rewrite `this` using `[hb]`. Conclude with `this`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨Y, hY, rfl⟩`. Conclude with `relC_fwd O cj _ _ _ _ h.C_mul hG (scA h) (by ext i j; rfl) (fun i j => scC_mem O _ _ h.cα_mem h.β'_mem j i) Y hY`.

Introduce `y hy`. Use `⟨(scPhi h).symm y, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[scPhi_symm_apply]`. Conclude with `relC_fwd O cj _ _ _ _ h.C'_mul hG' (scA' h) (by ext i j; rfl) (fun i j => scC_mem O _ _ h.αO h.βO j i) y hy`.
-/
theorem relG_map (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (relG O cj qi Zh T T').map (scPhi (r := r) h).toLinearMap = relG O cj qi (Zh * dlast r α) T T' := by
  have hG := gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh
  have hG' : gramG cj qi Zh T T' = (scC r (cj α) (-((α - 1) * qi * cj α))).transpose *
      gramG cj qi (Zh * dlast r α) T T' * (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    have := gramG_scale cj qi h.cjcj (cj α) T T' (by rw [h.cjcj, mul_comm]; exact h.αn) h.qic h.Tc h.T'c
      (Zh * dlast r α)
    rw [Matrix.mul_assoc, dlast_mul_cj h, Matrix.mul_one] at this
    have hb : (cj α - 1) * qi = -((α - 1) * qi * cj α) := by linear_combination qi * h.αn
    rw [hb] at this
    exact this
  apply le_antisymm
  · rintro _ ⟨Y, hY, rfl⟩
    exact relC_fwd O cj _ _ _ _ h.C_mul hG (scA h) (by ext i j; rfl)
      (fun i j => scC_mem O _ _ h.cα_mem h.β'_mem j i) Y hY
  · intro y hy
    refine ⟨(scPhi h).symm y, ?_, by simp⟩
    rw [scPhi_symm_apply]
    exact relC_fwd O cj _ _ _ _ h.C'_mul hG' (scA' h) (by ext i j; rfl)
      (fun i j => scC_mem O _ _ h.αO h.βO j i) y hy

def scBar (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    DDg O cj qi Zh T T' ≃ₗ[O] DDg O cj qi (Zh * dlast r α) T T' :=
  Submodule.Quotient.equiv _ _ (scPhi h) (relG_map h Zh)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scBar_mk (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y : Ix r → O) :
    scBar h Zh (Submodule.Quotient.mk Y) = Submodule.Quotient.mk (scPhi h Y) := rfl

/- English proof (translation)
Establish `hu : IsUnit α` using `⟨⟨α, cj α, h.αn, by rw [mul_comm]; exact h.αn⟩, rfl⟩`. Establish `hcu : IsUnit (cj α)` using `⟨⟨cj α, α, by rw [mul_comm]; exact h.αn, h.αn⟩, rfl⟩`. Establish `e1 : ∀ V : Ix r → O, (fun i => ((scPhi (r` using `r) h V i : O) : E)) = Matrix.vecMul (fun i => (V i : E)) ((scC r α ((α - 1) * qi)).map cj) := fun V => funext (scPhi_coe h V)`. Use `fG_invariant cj h.cjcj _ _ (scC r α ((α - 1) * qi)) (gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh) (by rw [scC_det]; exact hu) (by rw [show ((scC r α ((α - 1) * qi)).map cj).det = cj (scC r α ((α - 1) * qi)).det from (RingHom.map_det cj _).symm, scC_det]; exact hcu) ( …` as an intermediate fact. Rewrite `this` using `[← e1, ← e1]`.

Conclude with `this`.
-/
theorem formG_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y W : Ix r → O) :
    formG O cj qi (Zh * dlast r α) T T' (scPhi h Y) (scPhi h W) = formG O cj qi Zh T T' Y W := by
  have hu : IsUnit α := ⟨⟨α, cj α, h.αn, by rw [mul_comm]; exact h.αn⟩, rfl⟩
  have hcu : IsUnit (cj α) := ⟨⟨cj α, α, by rw [mul_comm]; exact h.αn, h.αn⟩, rfl⟩
  have e1 : ∀ V : Ix r → O, (fun i => ((scPhi (r := r) h V i : O) : E)) =
      Matrix.vecMul (fun i => (V i : E)) ((scC r α ((α - 1) * qi)).map cj) := fun V => funext (scPhi_coe h V)
  have := fG_invariant cj h.cjcj _ _ (scC r α ((α - 1) * qi))
    (gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh) (by rw [scC_det]; exact hu)
    (by rw [show ((scC r α ((α - 1) * qi)).map cj).det = cj (scC r α ((α - 1) * qi)).det from
      (RingHom.map_det cj _).symm, scC_det]; exact hcu) (fun i => (Y i : E)) (fun i => (W i : E))
  rw [← e1, ← e1] at this
  exact this

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (dlast_mul_cj h)]`.
-/
theorem inv_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (Zh * dlast r α)⁻¹ = dlast r (cj α) * Zh⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (dlast_mul_cj h)]

/- English proof (translation)
Unfold `lamC`. Rewrite using `[inv_scale h, ← Matrix.mulVec_mulVec, dlast, Matrix.mulVec_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem lamC_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) :
    lamC (Zh * dlast r α) y = cj α * lamC Zh y := by
  unfold lamC
  rw [inv_scale h, ← Matrix.mulVec_mulVec, dlast, Matrix.mulVec_diagonal]
  simp

/- English proof (translation)
Unfold `lamStarC`. Rewrite using `[inv_scale h]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[dlast, Matrix.diagonal_mul]`. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Simplify using `only [if_true, map_mul, h.cjcj]`. Take the linear combination `(cj (Zh⁻¹ (Fin.last r) (Fin.last r)) * y (Fin.last r)) * h.αn`. Simplify using `[hb]`.
-/
theorem lamStarC_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (y : Fin (r + 1) → E) :
    lamStarC cj (Zh * dlast r α) (fun b => cj (if b = Fin.last r then α else 1) * y b) = lamStarC cj Zh y := by
  unfold lamStarC
  rw [inv_scale h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dlast, Matrix.diagonal_mul]
  by_cases hb : b = Fin.last r
  · subst hb
    simp only [if_true, map_mul, h.cjcj]
    linear_combination (cj (Zh⁻¹ (Fin.last r) (Fin.last r)) * y (Fin.last r)) * h.αn
  · simp [hb]

end ScaleA5

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
