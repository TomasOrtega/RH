import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Minors

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Use `set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ`. Use `(pmat_isHermitian z).spectral_theorem` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`.

Establish `h1 : Uᴴ * U = 1` using `Unitary.coe_star_mul_self _`. Establish `h2 : U * Uᴴ = 1` using `Unitary.coe_mul_star_self _`. Establish `hinv : U⁻¹ = Uᴴ` using `Matrix.inv_eq_right_inv h2`. Establish `hu : IsUnit U` using `⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩`. Rewrite using `[hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]`.

Establish `he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ)`. Introduce `i`. Rewrite using `[Pi.exp_def, Complex.exp_eq_exp_ℂ]`. Simplify using `only [he]`. Rewrite using `[← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]`.
-/
theorem fbr_det_exp_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (NormedSpace.exp (pmat z)).det = 1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ := by
    have := (pmat_isHermitian z).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h2
  have hu : IsUnit U := ⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩
  rw [hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]
  have he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ) := by
    intro i
    rw [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  simp only [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]

/- English proof (translation)
Rewrite using `[toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul, (toMK_facts k).1, Matrix.det_one, mul_one]`.
-/
theorem fbr_det_conj {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * A * toMK k).det = A.det := by
  rw [toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul,
    (toMK_facts k).1, Matrix.det_one, mul_one]

/- English proof (translation)
Take `⟨hP, hE⟩` from `inP_conj k⁻¹ (pmat_inP z)`. Rewrite `hP`, `hE` using `[inv_inv]`. Rewrite using `[← hE]`. Use `set Y := toMK k⁻¹ * pmat z * toMK k with hY`. Use `set E := NormedSpace.exp Y with hEdef`.

Establish `hpd : E.PosDef` using `exp_noncompactPart_posDef hP`. Establish `hdet : lead n E = 1`. Establish `h1 : E.det = 1` using `by rw [hE, fbr_det_conj, fbr_det_exp_pmat]`. Unfold `lead`. Rewrite using `[dif_pos le_rfl]`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Both sides reduce to the same expression. Establish `hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re` using `fun i => (lead_posDef hpd _ i.isLt).1`. Establish `h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ)` using `fun i => Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])`.

Establish `hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ)`. Unfold `PhiM`. Rewrite using `[Complex.ofReal_prod]`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_zpow, ← h i]`.

Rewrite using `[hphi]`. Use `congr 1`. Establish `hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) = Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ))`. Introduce `i`. Rewrite using `[← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]`.

Rewrite using `[prod_congr rfl fun i _ => hz i, ← Real.exp_sum]`. Use `congr 1`. Use `set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg`. Establish `hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i`. Introduce `i`.

Distinguish the cases in `hi : (i : ℕ) + 1 < n`. Establish `hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩` using `by simp [muNext, hi]`. Establish `hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1` using `by simp [sCoef, hi]`. Rewrite using `[hm, hg]`. Simplify using `only`.

Rewrite using `[hs]`. Use `push_cast`. Rewrite using `[hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]`. Simplify using `only [rho]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : sCoef lam i = 0` using `by simp [sCoef, hi]`. Establish `hn : (i : ℕ) + 1 = n` using `by omega`. Rewrite using `[hg]`. Simplify using `only`.

Rewrite using `[hs, hn, hdet]`. Simplify using the standard rewrite rules. Rewrite using `[sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]`. Establish `hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i`. Use `symm`.

Use `sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_` and prove the remaining obligations. Introduce `i hi hi'`. Simplify using `only [mem_range] at hi hi'`. Establish `hs : sCoef lam i = 0` using `by simp only [sCoef]; rw [dif_neg (by omega)]`. Simplify using `[hg, hs]`.

Rewrite using `[hsub, Ph, ← sum_neg_distrib]`. Both sides reduce to the same expression.
-/
theorem fbr_phi {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PhiM μ (toMK k⁻¹ * NormedSpace.exp (pmat z) * toMK k) =
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) := by
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ (pmat_inP z)
  rw [inv_inv] at hP hE
  rw [← hE]
  set Y := toMK k⁻¹ * pmat z * toMK k with hY
  set E := NormedSpace.exp Y with hEdef
  have hpd : E.PosDef := exp_noncompactPart_posDef hP
  have hdet : lead n E = 1 := by
    have h1 : E.det = 1 := by rw [hE, fbr_det_conj, fbr_det_exp_pmat]
    unfold lead
    rw [dif_pos le_rfl]
    convert h1 using 2
    ext a b
    rfl
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re := fun i => (lead_posDef hpd _ i.isLt).1
  have h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← h i]
  rw [hphi]
  congr 1
  have hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) =
      Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ)) := by
    intro i
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]
  rw [prod_congr rfl fun i _ => hz i, ← Real.exp_sum]
  congr 1
  set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg
  have hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩ := by simp [muNext, hi]
      have hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1 := by simp [sCoef, hi]
      rw [hm, hg]
      simp only
      rw [hs]
      push_cast
      rw [hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]
      simp only [rho]
      push_cast
      ring
    · have hs : sCoef lam i = 0 := by simp [sCoef, hi]
      have hn : (i : ℕ) + 1 = n := by omega
      rw [hg]
      simp only
      rw [hs, hn, hdet]
      simp
  rw [sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]
  have hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i := by
    symm
    refine sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_
    intro i hi hi'
    simp only [mem_range] at hi hi'
    have hs : sCoef lam i = 0 := by simp only [sCoef]; rw [dif_neg (by omega)]
    simp [hg, hs]
  rw [hsub, Ph, ← sum_neg_distrib]
  rfl

/- English proof (translation)
Simplify using `only [psM, fF]`. Use `congr 1`. Use `congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)` and prove the remaining obligations. Rewrite using `[fbr_phi hμ k z]`.
-/
theorem psM_exp_pmat {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) {Λ : Fin n → ℝ}
    (T : KType ε Λ) (z : PCoord ε → ℂ) : psM T μ (NormedSpace.exp (pmat z)) = fF ε lam T (pmat z) := by
  simp only [psM, fF]
  congr 1
  refine congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)
  rw [fbr_phi hμ k z]

end ReciprocityTheory.ChartRestriction.DS
