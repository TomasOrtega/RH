import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.TraceGammaZeroEqOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[kroneckerMap_apply, conjTranspose_apply, mul_comm]`.
-/
theorem kron_conjTranspose' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext i j; simp [kroneckerMap_apply, conjTranspose_apply, mul_comm]

/- English proof (translation)
Establish `h` using `(hS n lam).2.1`. Rewrite `h`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite using `[Matrix.star_eq_conjTranspose, kron_conjTranspose', conjTranspose_one, ← mul_kronecker_mul, mul_one, ← Matrix.star_eq_conjTranspose, h, one_kronecker_one]`.
-/
theorem U_mem (hS : SwapLaws) :
    ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) ∈ Matrix.unitaryGroup (Ix n lam) ℂ := by
  have h := (hS n lam).2.1
  rw [Matrix.mem_unitaryGroup_iff] at h ⊢
  rw [Matrix.star_eq_conjTranspose, kron_conjTranspose', conjTranspose_one, ← mul_kronecker_mul, mul_one,
    ← Matrix.star_eq_conjTranspose, h, one_kronecker_one]

/- English proof (translation)
Use `set U := (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam`. Establish `hU` using `U_mem (lam := lam) hS`. Establish `hc : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U`. Introduce `k`. Rewrite using `[frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, swap_rhoW_k hu hS k]`.

Establish `hcomm` using `(hA n lam).2.2.2.2 U hU hc`. Establish `e : lefT n lam = clm lam U`. Rewrite using `[lefT_apply, cjL_apply, ← hcomm, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]`. Rewrite using `[e]`. Apply `ContinuousLinearMap.norm_map_of_mem_unitary` to reduce the goal to its premises.

Rewrite using `[Unitary.mem_iff]`. Establish `hs : star (clm lam U) = clm lam (star U)` using `(map_star _ U).symm`. Rewrite using `[hs, ← clm_mul', ← clm_mul', Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, clm_one']`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem Tiso_f (hu : IsUnit (sqQ lam)) (hA : Avg) (hS : SwapLaws) (v : EV n lam) : ‖lefT n lam v‖ = ‖v‖ := by
  set U := (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam
  have hU := U_mem (lam := lam) hS
  have hc : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U := by
    intro k
    rw [frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, swap_rhoW_k hu hS k]
  have hcomm := (hA n lam).2.2.2.2 U hU hc
  have e : lefT n lam = clm lam U := by
    rw [lefT_apply, cjL_apply, ← hcomm, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  rw [e]
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  rw [Unitary.mem_iff]
  have hs : star (clm lam U) = clm lam (star U) := (map_star _ U).symm
  rw [hs, ← clm_mul', ← clm_mul', Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, clm_one']
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Establish `h` using `((cjL lam).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn (hF n lam).2.2`. Conclude with `h`.
-/
theorem smooth_f (hF : MatrixFrechetDerivativeAtZeroLaws) : ContDiffOn ℝ ∞ (lefFr n lam) (GLs n) := by
  have h := ((cjL lam).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn (hF n lam).2.2
  exact h

/- English proof (translation)
Rewrite using `[lefFr_apply, (hF n lam).1, cj_one hu]`.
-/
theorem one_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) : lefFr n lam 1 = 1 := by
  rw [lefFr_apply, (hF n lam).1, cj_one hu]

/- English proof (translation)
Rewrite using `[lefFr_apply, lefFr_apply, lefFr_apply, cj_mul hu, (hF n lam).2.1 x y (isUnit_iff_ne_zero.mpr hx) (isUnit_iff_ne_zero.mpr hy)]`.
-/
theorem mul_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) (x : Mat n) (hx : x ∈ GLs n) (y : Mat n) (hy : y ∈ GLs n) :
    lefFr n lam (x * y) = lefFr n lam x * lefFr n lam y := by
  rw [lefFr_apply, lefFr_apply, lefFr_apply, cj_mul hu,
    (hF n lam).2.1 x y (isUnit_iff_ne_zero.mpr hx) (isUnit_iff_ne_zero.mpr hy)]

/- English proof (translation)
Rewrite using `[lefS_apply, hScal n]`. Both sides reduce to the same expression.
-/
theorem lefS_diag (hScal : GamScal) (s : ℝ) : lefS n lam s =
    cjL lam (krL n lam (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)) := by
  rw [lefS_apply, hScal n]; rfl

/- English proof (translation)
Establish `e : lefS n lam = fun s : ℝ => (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap) (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)`. Use function extensionality and compare the values at `s`. Rewrite using `[lefS_diag hScal]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `ContinuousLinearMap.contDiff _ |>.comp ?_` and prove the remaining obligations. Use `contDiff_pi.2 fun A => contDiff_pi.2 fun B => ?_` and prove the remaining obligations. Distinguish the cases in `h : A = B`. Substitute `h` using the available equality. Simplify using `only [diagonal_apply_eq]`.

Conclude with `(Complex.ofRealCLM.contDiff).pow _`. Simplify using `only [diagonal_apply_ne _ h]`. Conclude with `contDiff_const`.
-/
theorem Ssmooth_f (hScal : GamScal) : ContDiff ℝ ∞ (lefS n lam) := by
  have e : lefS n lam = fun s : ℝ => (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
      (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  rw [e]
  refine ContinuousLinearMap.contDiff _ |>.comp ?_
  refine contDiff_pi.2 fun A => contDiff_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]; exact (Complex.ofRealCLM.contDiff).pow _
  · simp only [diagonal_apply_ne _ h]; exact contDiff_const

/- English proof (translation)
Use `hasDerivAt_pi.2 fun A => hasDerivAt_pi.2 fun B => ?_` and prove the remaining obligations. Distinguish the cases in `h : A = B`. Substitute `h` using the available equality. Simplify using `only [diagonal_apply_eq]`. Conclude with `(hasDerivAt_pow A.card (s : ℂ)).comp_ofReal`.

Simplify using `only [diagonal_apply_ne _ h]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_diagPow (s : ℝ) : HasDerivAt (fun s : ℝ => (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card))
    (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1)) s := by
  refine hasDerivAt_pi.2 fun A => hasDerivAt_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]
    exact (hasDerivAt_pow A.card (s : ℂ)).comp_ofReal
  · simp only [diagonal_apply_ne _ h]; exact hasDerivAt_const _ _

/- English proof (translation)
Use `set L := (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)`. Establish `e : lefS n lam = fun s : ℝ => L (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)`. Use function extensionality and compare the values at `s`. Rewrite using `[lefS_diag hScal]`. Both sides reduce to the same expression.

Establish `hd : HasDerivAt (lefS n lam) (L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))) s`. Rewrite using `[e]`. Conclude with `L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_diagPow s)`. Rewrite using `[hd.deriv]`. Establish `hcf : ∀ p : Fin n × Fin n, cf n (hb p) = Pi.single (finProdFinEquiv p) 1` using `fun p => by`.

Use `Cxa.cf_hbM (n := n) (finProdFinEquiv p)` as an intermediate fact. Simplify `this` using `[hbM]`. Establish `key : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) * annL n (cf n (hb p)) = Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1)`. Rewrite using `[← hN n (s : ℂ)]`. Conclude with `Fintype.sum_equiv finProdFinEquiv _ _ (fun p => by rw [hcf p])`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[lefε_apply, lefι_apply, lefS_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem Sder_f (hu : IsUnit (sqQ lam)) (hScal : GamScal) (hN : Number) (s : ℝ) :
    deriv (lefS n lam) s = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
  set L := (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
  have e : lefS n lam = fun s : ℝ => L (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  have hd : HasDerivAt (lefS n lam) (L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))) s := by
    rw [e]; exact L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_diagPow s)
  rw [hd.deriv]
  have hcf : ∀ p : Fin n × Fin n, cf n (hb p) = Pi.single (finProdFinEquiv p) 1 := fun p => by
    have := Cxa.cf_hbM (n := n) (finProdFinEquiv p)
    simpa [hbM] using this
  have key : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
      annL n (cf n (hb p)) = Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1) := by
    rw [← hN n (s : ℂ)]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun p => by rw [hcf p])
  calc L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))
      = cjL lam (krL n lam (∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [key]; rfl
    _ = ∑ p : Fin n × Fin n, cjL lam (krL n lam (creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [map_sum, map_sum]
    _ = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lefε_apply, lefι_apply, lefS_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul,
          mul_one, mul_one]
        rfl

end PositivityTheory.RgBcC
