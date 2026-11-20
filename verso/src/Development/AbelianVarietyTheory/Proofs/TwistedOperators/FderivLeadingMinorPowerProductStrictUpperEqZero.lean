import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.PhiUpperDeriv

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableAt_const _`. Consider the case `insert a s ha ih`.

Simplify using `only [Finset.prod_insert ha]`. Conclude with `(h a).mul ih`.
-/
theorem differentiableAt_prod {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset ι)
    {f : ι → E → ℂ} {z : E} (h : ∀ i, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, f i y) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

/- English proof (translation)
Establish `hent : ∀ a b : Fin n, DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) z`. Introduce `a b`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ` to `{ toFun := fun y => y a b map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `(LinearMap.toContinuousLinearMap L).differentiableAt`. Establish `hexp : (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) = fun y => ∑ σ : Equiv.Perm (Fin l), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)`.

Use function extensionality and compare the values at `y`. Simplify using `only [leadMinor, Matrix.det_apply', Matrix.submatrix_apply]`. Rewrite using `[hexp]`. Establish `key : ∀ σ : Equiv.Perm (Fin l), DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z` using `fun σ => (differentiableAt_prod Finset.univ fun i => hent _ _).const_mul _`. Establish `hsum` using `DifferentiableAt.sum (u := Finset.univ) fun σ _ => key σ`.

Rewrite `hsum` using `[Finset.sum_fn]`. Conclude with `hsum`.
-/
theorem differentiableAt_leadMinor {n : ℕ} (l : ℕ) (hl : l ≤ n) (z : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) z := by
  have hent : ∀ a b : Fin n, DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) z := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun y => y a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt
  have hexp : (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) = fun y =>
      ∑ σ : Equiv.Perm (Fin l), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i) := by
    funext y
    simp only [leadMinor, Matrix.det_apply', Matrix.submatrix_apply]
  rw [hexp]
  have key : ∀ σ : Equiv.Perm (Fin l), DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z :=
    fun σ => (differentiableAt_prod Finset.univ fun i => hent _ _).const_mul _
  have hsum := DifferentiableAt.sum (u := Finset.univ) fun σ _ => key σ
  rw [Finset.sum_fn] at hsum
  exact hsum

/- English proof (translation)
Establish `hPhi : Phi lam = fun z => ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i))`. Use function extensionality and compare the values at `fun _ => rfl`. Rewrite using `[hPhi]`. Use `differentiableAt_prod Finset.univ fun i => ?_` and prove the remaining obligations. Conclude with `(differentiableAt_leadMinor (i.val + 1) i.isLt y).zpow (Or.inl (hy i))`.
-/
theorem differentiableAt_Phi {n : ℕ} (lam : Fin n → ℝ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n) :
    DifferentiableAt ℂ (Phi lam) y := by
  have hPhi : Phi lam = fun z => ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i)) :=
    funext fun _ => rfl
  rw [hPhi]
  refine differentiableAt_prod Finset.univ fun i => ?_
  exact (differentiableAt_leadMinor (i.val + 1) i.isLt y).zpow (Or.inl (hy i))

/- English proof (translation)
Establish `hline : y + t • (y * N) = 1 * y * (1 + t • N)`. Rewrite using `[Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Establish `hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ)` using `fun i j hij => Matrix.one_apply_ne (ne_of_lt hij)`. Establish `hup : IsUp (1 + t • N)` using `fun i j hji => by`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, hN i j hji.le, Matrix.one_apply_ne (ne_of_gt hji)]`.

Simplify using the standard rewrite rules. Establish `hdiag : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • N) l l ≠ 0` using `fun l => by`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]`. Simplify using the standard rewrite rules. Take `⟨-, hval⟩` from `GlobalTheory.PhiTriangular.phiTri n lam 1 y (1 + t • N) hlo hup hdiag hy`.

Rewrite using `[hline, hval]`. Establish `hone : ∀ l, ((1 : Matrix (Fin n) (Fin n) ℂ) l l * (1 + t • N) l l) = 1` using `fun l => by`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]`. Simplify using the standard rewrite rules. Simplify using `only [hone, _root_.one_zpow, Finset.prod_const_one, one_mul]`.
-/
theorem Phi_mul_unipotent {n : ℕ} (lam : Fin n → ℝ) {y N : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n)
    (hN : ∀ i i' : Fin n, i' ≤ i → N i i' = 0) (t : ℂ) : Phi lam (y + t • (y * N)) = Phi lam y := by
  have hline : y + t • (y * N) = 1 * y * (1 + t • N) := by
    rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ) := fun i j hij =>
    Matrix.one_apply_ne (ne_of_lt hij)
  have hup : IsUp (1 + t • N) := fun i j hji => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN i j hji.le, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  have hdiag : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • N) l l ≠ 0 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  obtain ⟨-, hval⟩ := GlobalTheory.PhiTriangular.phiTri n lam 1 y (1 + t • N) hlo hup hdiag hy
  rw [hline, hval]
  have hone : ∀ l, ((1 : Matrix (Fin n) (Fin n) ℂ) l l * (1 + t • N) l l) = 1 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  simp only [hone, _root_.one_zpow, Finset.prod_const_one, one_mul]

/- English proof (translation)
Introduce `n lam y N hy hN`. Establish `hD : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) y) y` using `(differentiableAt_Phi lam hy).hasFDerivAt`. Establish `hL : HasDerivAt (fun t : ℂ => y + t • (y * N)) (y * N) 0`. Establish `h1` using `((hasDerivAt_id (0 : ℂ)).smul_const (y * N)).const_add y`. Simplify `h1` using `only [one_smul, id]`.

Establish `hcomp : HasDerivAt (fun t : ℂ => Phi lam (y + t • (y * N))) (fderiv ℂ (Phi lam) y (y * N)) 0` using `hD.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)`. Establish `hconst : (fun t : ℂ => Phi lam (y + t • (y * N))) = fun _ => Phi lam y`. Use function extensionality and compare the values at `fun t => Phi_mul_unipotent lam hy hN t`. Rewrite `hcomp` using `[hconst]`. Conclude with `hcomp.unique (hasDerivAt_const 0 (Phi lam y))`.
-/
theorem fderiv_Phi_upper : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n →
    (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  intro n lam y N hy hN
  have hD : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) y) y := (differentiableAt_Phi lam hy).hasFDerivAt
  have hL : HasDerivAt (fun t : ℂ => y + t • (y * N)) (y * N) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).smul_const (y * N)).const_add y
    simpa only [one_smul, id] using h1
  have hcomp : HasDerivAt (fun t : ℂ => Phi lam (y + t • (y * N))) (fderiv ℂ (Phi lam) y (y * N)) 0 :=
    hD.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hconst : (fun t : ℂ => Phi lam (y + t • (y * N))) = fun _ => Phi lam y :=
    funext fun t => Phi_mul_unipotent lam hy hN t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (Phi lam y))

end GlobalTheory.PhiUpperDeriv
