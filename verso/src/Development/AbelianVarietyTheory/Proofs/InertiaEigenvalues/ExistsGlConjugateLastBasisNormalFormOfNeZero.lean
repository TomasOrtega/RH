import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem full_blocks {r : ℕ} {k : Type} [CommRing k] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    full (blocks A) = A := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [full, blocks, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc,
      finSumFinEquiv_symm_last]

def nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.of fun i j => if i = Fin.last r then c j else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem nfMat_mulVec_castSucc {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by
  simp only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [h]
  · simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem nfMat_injective {r : ℕ} {k : Type} [Field k] (c : Fin (r + 1) → k) (h0 : c 0 ≠ 0) :
    Function.Injective (nfMat c).mulVec := by
  intro x y hxy
  set v := x - y with hv
  have key : nfMat c *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hxy, sub_self]
  have hs : ∀ i : Fin r, v i.succ = 0 := fun i => by
    rw [← nfMat_mulVec_castSucc c v i, key]; rfl
  have hl : c ⬝ᵥ v = 0 := by rw [← nfMat_mulVec_last c v, key]; rfl
  have h0v : v 0 = 0 := by
    rw [dotProduct, Fin.sum_univ_succ] at hl
    simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left h0
  have : v = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => exact h0v
    | succ i => exact hs i
  exact sub_eq_zero.mp this

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem eL_vecMul_nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem shiftCompanionLastRowMatrix_mulVec_firstBasis {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [nfMat, Matrix.mulVec, dotProduct, eL]
  | cast i =>
    rw [nfMat_mulVec_castSucc]
    simp [eL, Pi.single_apply, Fin.castSucc_ne_last]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem glNormal_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 →
    ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  intro k _ r a h0
  have hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1) :=
    Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)
  refine ⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩
  have hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1 := rfl
  have hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1 := GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1
  unfold act sec GlobalTheory.JR.Step.lift
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (GlobalTheory.JR.Step.full_blocks _).symm
  · simp only [hg]; exact GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1
  · show a.2.1 ᵥ* _ = _
    have hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
      exact hu.unit.mul_inv
    have e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ*
        ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k := by
      rw [Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]
    rw [hinv] at e
    exact e

end GlobalTheory.JR.Step
