import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

/- English proof (translation)
Establish `e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1)`. Establish `h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1)`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]`. Simplify using `only [Matrix.mul_assoc]`. Unfold `expM`.

Rewrite using `[conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this]`. Use `module`. Rewrite using `[e]`.

Conclude with `hQ.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))`.
-/
theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

/- English proof (translation)
Establish `hi' : g' * g = 1` using `mul_eq_one_comm.1 hi`. Establish `h1 : gᴴ * H = H * g'`. Combine the equalities or inequalities in the displayed calculation. Establish `hc' : g' * s = s * g'`. Combine the equalities or inequalities in the displayed calculation.

Establish `a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x)` using `fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]`. Establish `a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x)` using `fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]`. Establish `a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x)` using `fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]`. Establish `a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x` using `fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]`. Establish `a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x` using `fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]`.

Unfold `expM`. Simplify using `only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]`. Use `module`.
-/
theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

/- English proof (translation)
Establish `e1 : (g - 1) *ᵥ z = g *ᵥ z - z` using `by rw [sub_mulVec, one_mulVec]`. Establish `e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)`. Rewrite using `[← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`. Establish `e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z))`. Rewrite using `[mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]`.

Establish `e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w)` using `fun w => by`. Rewrite using `[star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]`. Simplify using the standard rewrite rules. Establish `e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0` using `(Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm`. Unfold `expM`.

Rewrite using `[smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]`. Generalize the expression as in `star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5`. Generalize the expression as in `star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w`. Apply the tactic sequence `apply Complex.ext <;> simp [e5] <;> ring`.
-/
theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

/- English proof (translation)
Establish `h0` using `(GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1`. Establish `h1` using `congrArg det (expM_mul hH hs hg hc hi)`. Rewrite `h1` using `[det_mul, det_mul, det_mul]`. Establish `h2 : (-H).det * (-s).det = (H * s).det` using `by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Establish `h3` using `hQ.det_pos`.

Establish `h4 : ((H * s).det.re : ℂ) = (H * s).det` using `Complex.ext rfl (Complex.pos_iff.1 h3).2`. Rewrite using `[Complex.ofReal_inv, h4]`. Establish `h5` using `h3.ne'`. Unfold `dP`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← h2]`. Take the linear combination `(-(-s).det) * h1`.
-/
theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL

omit [DecidableEq O] in

/- English proof (translation)
Use `haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance`. Use `haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Set `e` to `unvE O m n`. Establish `he : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`.

Establish `hm` using `Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)`. Establish `hp` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)`. Generalize the expression as in `Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp`. Use `⟨?_, c, hp, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`.

Conclude with `(he.integrable_map_iff.2 hf).smul_measure_nnreal`. Use `conv_lhs => rw [hm]`. Rewrite using `[integral_smul_nnreal_measure, he.integral_map]`. Both sides reduce to the same expression.
-/
theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

/- English proof (translation)
The claim follows from `det_blockDiagonal _`.
-/
theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

/- English proof (translation)
Unfold `RealWeil.blk`. Rewrite using `[← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]`. Both sides reduce to the same expression.
-/
theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

/- English proof (translation)
Establish `h1 : a'ᴴ * aᴴ = 1` using `by rw [← conjTranspose_mul, hi, conjTranspose_one]`. Establish `h2 : G * a = a'ᴴ * G` using `by conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Use `(inv_eq_right_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]`.
-/
theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
/- English proof (translation)
Establish `e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z)` using `funext fun τ => (cpt_blk b a z τ).symm`. Establish `e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w)` using `fun w => funext fun τ => by show Complex.I • (sT τ * cpt w τ * sS τ) = _`. Rewrite using `[← cpt_blk]`. Both sides reduce to the same expression. Unfold `gaussR`.

Rewrite using `[dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring

open Classical in

/- English proof (translation)
Introduce `D S T sS sT hS hT`. Use `⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩` and prove the remaining obligations. Take `⟨hs, hQ⟩` from `HM_cartan hS hT`. Establish `hd : (blk b a - 1).det ≠ 0`. Rewrite using `[det_blk_sub_one]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2`. Establish `hi : blk b a * blk b' a' = 1`. Rewrite using `[blk_mul, ← blk_one]`. Apply the tactic sequence `congr 1 <;> funext τ`. Conclude with `(h τ).2.1`.

Conclude with `mul_eq_one_comm.1 (h τ).1`. Establish `hc : blk sT sS * blk b a = blk b a * blk sT sS`. Rewrite using `[blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext τ`. Conclude with `(h τ).2.2.2.2.2.1`.

Conclude with `(h τ).2.2.2.2.1.symm`. Establish `hg : (blk b a)ᴴ * HM S T * blk b a = HM S T`. Unfold `HM`. Rewrite using `[blk_conjTranspose, blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext τ`.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]`. Conclude with `inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1`. Take `⟨-, h1, h2⟩` from `GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)`. Simplify using `only [← gaussR_unv hQ] at h1 h2`. Take `⟨h3, c, hc0, h4⟩` from `integral_unv _ h1`.

Use `⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩` and prove the remaining obligations. Rewrite using `[h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk, ← detPlus_blockDiagonal, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
