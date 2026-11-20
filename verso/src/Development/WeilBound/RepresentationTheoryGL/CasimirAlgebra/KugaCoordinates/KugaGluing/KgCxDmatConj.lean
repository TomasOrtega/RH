import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgLieOpComm

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
/- English proof (translation)
Unfold `atEmb`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.star_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem kg_star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (starRingEnd ℂ z) := by
  classical
  unfold atEmb
  funext w
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ = Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z))))`. Introduce `z`. Rewrite using `[← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]`. Establish `e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) = -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I)))`. Rewrite using `[← map_neg]`.

Use `congr 1`. Use function extensionality and compare the values at `k l`. Use `show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)`. Rewrite using `[Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]`. Apply the tactic sequence `split_ifs <;> simp`.

Unfold `cx`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one, Complex.conj_I, e2]`. Simplify using `only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]`. Use `module`.
-/
theorem kg_cx_dmat_conj (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ)
    (τ : E →+* ℂ) (i j : Fin a) : (cx τ Ξ.dmat i j)ᴴ = cx τ Ξ.dmat j i := by
  have e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ =
      Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z)))) := by
    intro z; rw [← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]
  have e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) =
      -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I))) := by
    rw [← map_neg]
    congr 1
    funext k l
    show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)
    rw [Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]
    split_ifs <;> simp
  unfold cx
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one,
    Complex.conj_I, e2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  module

/- English proof (translation)
Simplify using `only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]`.
-/
theorem kg_cas_herm (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) (τ : E →+* ℂ) :
    (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)ᴴ = ∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]

omit [NumberField E] in
/- English proof (translation)
Use extensionality with `i j w`. Establish `h : star (X j i) = X i j` using `by rw [← Matrix.star_apply, hX]`. Establish `h' : star (X j i w) = X i j w` using `congrFun h w`. Simplify using `only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul, Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kg_star_iM {X : Matrix (Fin a) (Fin a) (Cinf E)} (hX : star X = X) : star (iM X) = -iM X := by
  ext i j w
  have h : star (X j i) = X i j := by rw [← Matrix.star_apply, hX]
  have h' : star (X j i w) = X i j w := congrFun h w
  simp only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul,
    Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]
  ring

def kgL : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a where
  toFun := toL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField E] in

def kgD (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) : Herm E a →ₗ[ℝ] Herm E a where
  toFun Y := ⟨Z * Y.1 - Y.1 * Z, by
    have hY : star Y.1 = Y.1 := Y.2
    show star (Z * Y.1 - Y.1 * Z) = Z * Y.1 - Y.1 * Z
    rw [star_sub, star_mul, star_mul, hY, hZ, mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub]⟩
  map_add' Y Y' := Subtype.ext (by
    show Z * (Y.1 + Y'.1) - (Y.1 + Y'.1) * Z = (Z * Y.1 - Y.1 * Z) + (Z * Y'.1 - Y'.1 * Z)
    rw [mul_add, add_mul]; abel)
  map_smul' c Y := Subtype.ext (by
    show Z * (c • Y.1) - (c • Y.1) * Z = c • (Z * Y.1 - Y.1 * Z)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub])

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kgD_val (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) :
    (kgD Z hZ Y).1 = Z * Y.1 - Y.1 * Z := rfl

end
end PositivityTheory.Rg.Cz
