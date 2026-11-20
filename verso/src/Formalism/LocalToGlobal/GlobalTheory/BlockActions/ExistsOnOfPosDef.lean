import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG
open scoped ComplexOrder

/- English proof (translation)
Use `set U : Matrix (Fin k) (Fin k) ℂ := (hH.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hUdef`. Establish `hUU : star U * U = 1` using `Unitary.star_mul_self_of_mem (hH.1.eigenvectorUnitary).2`. Establish `hd : star U * H * U = diagonal (RCLike.ofReal ∘ hH.1.eigenvalues)`. Establish `h` using `hH.1.conjStarAlgAut_star_eigenvectorUnitary`. Rewrite `h` using `[Unitary.conjStarAlgAut_star_apply]`.

Simplify `h` using `[hUdef]`. Set `d : Fin k → ℂ` to `fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)`. Establish `hpos : ∀ i, 0 < hH.1.eigenvalues i` using `fun i => hH.eigenvalues_pos i`. Use `⟨U * diagonal d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal]`.

Use `IsUnit.mul ?_ (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))` and prove the remaining obligations. Establish `h1 : U.det * (star U).det = 1`. Rewrite using `[← Matrix.det_mul, Unitary.mul_star_self_of_mem (hH.1.eigenvectorUnitary).2, Matrix.det_one]`. Conclude with `⟨Units.mkOfMulEqOne _ _ h1, rfl⟩`. Simplify using `only [d, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]`.

Conclude with `(Real.sqrt_pos.mpr (hpos i)).ne'`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.star_eq_conjTranspose]`. Establish `e : diagonal (star d) * star U * H * (U * diagonal d) = diagonal (star d) * (star U * H * U) * diagonal d`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hs : Real.sqrt (hH.1.eigenvalues i) ≠ 0` using `(Real.sqrt_pos.mpr (hpos i)).ne'`. Establish `hr : (Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ = 1`. Rewrite using `[mul_comm ((Real.sqrt (hH.1.eigenvalues i))⁻¹) (hH.1.eigenvalues i), mul_assoc, ← mul_inv, Real.mul_self_sqrt (hpos i).le, mul_inv_cancel₀ (hpos i).ne']`.

Establish `h2 : (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hH.1.eigenvalues i : ℝ) : ℂ) * (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1` using `by exact_mod_cast hr`. Simplify using `only [d, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]`. Conclude with `h2`.
-/
theorem exists_on_of_posDef {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.PosDef) :
    ∃ o : Matrix (Fin k) (Fin k) ℂ, IsUnit o.det ∧ oᴴ * H * o = 1 := by
  classical
  set U : Matrix (Fin k) (Fin k) ℂ := (hH.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.1.eigenvectorUnitary).2
  have hd : star U * H * U = diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) := by
    have h := hH.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hUdef] using h
  let d : Fin k → ℂ := fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hpos : ∀ i, 0 < hH.1.eigenvalues i := fun i => hH.eigenvalues_pos i
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul ?_ (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))
    · have h1 : U.det * (star U).det = 1 := by
        rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem (hH.1.eigenvectorUnitary).2, Matrix.det_one]
      exact ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
    · simp only [d, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
      exact (Real.sqrt_pos.mpr (hpos i)).ne'
  · rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.star_eq_conjTranspose]
    have e : diagonal (star d) * star U * H * (U * diagonal d) = diagonal (star d) * (star U * H * U) * diagonal d := by
      simp only [Matrix.mul_assoc]
    rw [e, hd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hH.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    have hr : (Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ = 1 := by
      rw [mul_comm ((Real.sqrt (hH.1.eigenvalues i))⁻¹) (hH.1.eigenvalues i), mul_assoc, ← mul_inv,
        Real.mul_self_sqrt (hpos i).le, mul_inv_cancel₀ (hpos i).ne']
    have h2 : (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hH.1.eigenvalues i : ℝ) : ℂ) *
        (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    simp only [d, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    exact h2

variable {D : D7}

/- English proof (translation)
The claim follows from `D.sp.cm.cmUnram.2.1 (embT D τ) x`.
-/
theorem embT_sig (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]`. Rewrite using `[embT_sig]`. Both sides reduce to the same expression.
-/
theorem map_cT {m n : Type} (M : Matrix m n D.host.E) (τ : D.what₂.Tau) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [embT_sig]
  rfl

variable (D) in

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[gramOf_apply]`. Establish `hc : ∀ i : Fin (D.R.N D.R.m - 1), (fun k => iXm D k i) = iXc D (Pi.single i 1)`. Introduce `i`. Use function extensionality and compare the values at `k`.

Simplify using `only [iXm, LinearMap.toMatrix'_apply]`. Rewrite using `[hc, hc, hform_iXc]`. Simplify using `[hform, Pi.single_apply]`.
-/
theorem gramP_eq : gramP D = ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * iXm D := by
  ext a b
  rw [gramOf_apply]
  have hc : ∀ i : Fin (D.R.N D.R.m - 1), (fun k => iXm D k i) = iXc D (Pi.single i 1) := by
    intro i; funext k; simp only [iXm, LinearMap.toMatrix'_apply]
  rw [hc, hc, hform_iXc]
  simp [hform, Pi.single_apply]

variable (D) in

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (iXc D) (LinearMap.ker_eq_bot.mpr (iXc_injective D))`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Rewrite using `[iXm, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`.
-/
theorem iXm_leftInv : ∃ L : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, L * iXm D = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (iXc D) (LinearMap.ker_eq_bot.mpr (iXc_injective D))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [iXm, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

/- English proof (translation)
Take `⟨C, hC, -, -⟩` from `(Tf.val D.R.m le_rfl (Or.inr rfl)).de`. Establish `hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl` using `hC`. Take `⟨L, hL⟩` from `iXm_leftInv D`. Use `set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map (embT D τ) with hA`. Establish `hG : gramC (gramP D) (embT D) τ = Aᴴ * A`.

Establish `e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D = ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D)`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [gramC]`. Rewrite using `[gramP_eq, ← hC', e1, Matrix.map_mul, map_cT, hA]`.

Establish `hinj : Function.Injective A.mulVec`. Introduce `x y hxy`. Establish `hCi : IsUnit C.1.det` using `(Matrix.isUnit_iff_isUnit_det _).mp C.isUnit`. Establish `h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map (embT D τ) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h2` using `congrArg (fun v => ((L * C.1⁻¹).map (embT D τ)) *ᵥ v) hxy`. Simplify using `only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2`. Conclude with `h2`. Rewrite using `[hG]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self A hinj`.
-/
theorem gramP_posDef {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (τ : D.what₂.Tau) : (gramC (gramP D) (embT D) τ).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map (embT D τ) with hA
  have hG : gramC (gramP D) (embT D) τ = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    simp only [gramC]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map (embT D τ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map (embT D τ)) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

/- English proof (translation)
Establish `h` using `fun τ => exists_on_of_posDef (k := D.R.N D.R.m - 1) (gramC (gramP D) (embT D) τ) (gramP_posDef Tf τ)`. Use `choose o ho1 ho2 using h`. Conclude with `⟨⟨o, ho1⟩, ho2⟩`.
-/
theorem exists_onP {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    ∃ o : FrP D, ∀ τ, (o.1 τ)ᴴ * gramC (gramP D) (embT D) τ * o.1 τ = 1 := by
  have h := fun τ => exists_on_of_posDef (k := D.R.N D.R.m - 1) (gramC (gramP D) (embT D) τ) (gramP_posDef Tf τ)
  choose o ho1 ho2 using h
  exact ⟨⟨o, ho1⟩, ho2⟩

end Formalism.L2.GlobalTheoryTheory.Br
