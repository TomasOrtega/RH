import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[full, blocks, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`.
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
Simplify using `only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]`. Rewrite using `[Finset.sum_eq_single i.succ]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg]`.

Use the proof step `· simp`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Use `ext`. Simplify using `[h]`.

Simplify using the standard rewrite rules.
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
Simplify using `[Matrix.mulVec, dotProduct, nfMat]`.
-/
theorem nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]

/- English proof (translation)
Introduce `x y hxy`. Use `set v := x - y with hv`. Establish `key : nfMat c *ᵥ v = 0` using `by rw [hv, Matrix.mulVec_sub, hxy, sub_self]`. Establish `hs : ∀ i : Fin r, v i.succ = 0` using `fun i => by`. Rewrite using `[← nfMat_mulVec_castSucc c v i, key]`.

Both sides reduce to the same expression. Establish `hl : c ⬝ᵥ v = 0` using `by rw [← nfMat_mulVec_last c v, key]; rfl`. Establish `h0v : v 0 = 0`. Rewrite `hl` using `[dotProduct, Fin.sum_univ_succ]`. Simplify using `only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl`.

Conclude with `(mul_eq_zero.mp hl).resolve_left h0`. Establish `: v = 0`. Use function extensionality and compare the values at `j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact h0v`.

Consider the case `succ i => exact hs i`. Conclude with `sub_eq_zero.mp this`.
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
Use function extensionality and compare the values at `j`. Simplify using `[eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]`.
-/
theorem eL_vecMul_nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [nfMat, Matrix.mulVec, dotProduct, eL]`. Consider the case `cast i`. Rewrite using `[nfMat_mulVec_castSucc]`.

Simplify using `[eL, Pi.single_apply, Fin.castSucc_ne_last]`.
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
Introduce `k _ r a h0`. Establish `hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1)` using `Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)`. Use `⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩` and prove the remaining obligations. Establish `hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1` using `rfl`. Establish `hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1` using `GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1`.

Unfold `act sec GlobalTheory.JR.Step.lift`. Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))` and prove the remaining obligations. Conclude with `(GlobalTheory.JR.Step.full_blocks _).symm`. Simplify using `only [hg]`. Conclude with `GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1`.

Use `show a.2.1 ᵥ* _ = _`. Establish `hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1`. Conclude with `hu.unit.mul_inv`. Establish `e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ* ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k`. Rewrite using `[Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]`.

Rewrite `e` using `[hinv]`. Conclude with `e`.
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
