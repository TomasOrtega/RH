import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
private lemma gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Rewrite using `[gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
private lemma gram_mul_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite `hx`, the goal using `[X.mem_dom_iff]`. Introduce `τ`. Establish `hN` using `FrameDegreeData.upper_of_bor (X := X) hb τ`. Establish `hbd` using `(hb τ).1`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations.

Use `show (mat x τ * mat b τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hx τ).1 hbd`. Establish `hd` using `(hx τ).2 i`. Establish `hdiag : ∀ j, mat b τ j j ≠ 0`.

Introduce `j`. Rewrite `hbd` using `[Matrix.det_of_upperTriangular hN]`. Conclude with `Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)`. Establish `hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hdiag _`. Establish `heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i * (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ)` using `by show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _`.

Rewrite using `[gram_mul_lemma_2, FrameDegreeData.lminor_conj hN, show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]`. Both sides reduce to the same expression. Rewrite using `[heq, Complex.re_mul_ofReal, ← mul_assoc]`. Conclude with `mul_pos hd (Complex.normSq_pos.2 hP0)`.
-/
theorem dom_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  have hN := FrameDegreeData.upper_of_bor (X := X) hb τ
  have hbd := (hb τ).1
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hbd
  · have hd := (hx τ).2 i
    have hdiag : ∀ j, mat b τ j j ≠ 0 := by
      intro j
      rw [Matrix.det_of_upperTriangular hN] at hbd
      exact Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)
    have hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i *
        (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
          (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ) := by
      show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _
      rw [gram_mul_lemma_2, FrameDegreeData.lminor_conj hN,
        show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]
      rfl
    rw [heq, Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos hd (Complex.normSq_pos.2 hP0)

/- English proof (translation)
Establish `hst` using `(X.Γ_stab γ hγ).1`. Use extensionality with `i j`. Establish `h` using `hst (Pi.single i 1) (Pi.single j 1)`. Establish `hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j`. Simplify using `[herm, Pi.single_apply, cc, apply_ite]`.

Establish `hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) = ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j`. Simplify using `only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← hL, h, hR]`.
-/
theorem stab_mat {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hst := (X.Γ_stab γ hγ).1
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  have hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, cc, apply_ite]
  have hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← hL, h, hR]

/- English proof (translation)
Establish `h` using `stab_mat X hγ`. Rewrite using `[gram_eq_lemma]`. Use `conv_rhs => rw [← h]`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]`.
-/
theorem gram_gam {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1) = X.Gm.map τ.1 := by
  have h := stab_mat X hγ
  rw [gram_eq_lemma]
  conv_rhs => rw [← h]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]

/- English proof (translation)
Use `show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _`. Rewrite using `[gram_mul_lemma_2, gram_gam X hγ τ, gram_eq_lemma]`.
-/
theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _
  rw [gram_mul_lemma_2, gram_gam X hγ τ, gram_eq_lemma]

/- English proof (translation)
Rewrite `hx`, the goal using `[X.mem_dom_iff]`. Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Use `mul_ne_zero ?_ (hx τ).1` and prove the remaining obligations. Establish `h1 : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Conclude with `(map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero`. Use `(hx τ).2 i` as an intermediate fact. Simplify `this` using `only [dmin, gram_lact X hγ x τ]`.
-/
theorem dom_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have h1 : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]
      rfl
    rw [h1]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have := (hx τ).2 i
    simpa only [dmin, gram_lact X hγ x τ] using this

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
