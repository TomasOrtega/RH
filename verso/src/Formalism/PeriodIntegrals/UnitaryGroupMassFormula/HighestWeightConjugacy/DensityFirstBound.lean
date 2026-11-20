import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.CayMulConjTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensitySecondBound

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

/- English proof (translation)
Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), map_one]`.
-/
theorem mapMatrix_inv (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) (h : M.det ≠ 0) :
    f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), map_one]

/- English proof (translation)
The claim follows from `(RingHom.map_det f M).symm`.
-/
theorem det_mapMatrix (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) : (f.mapMatrix M).det = f M.det :=
  (RingHom.map_det f M).symm

variable [IsCMField L]

def skewL (b : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  b - ((IsCMField.complexConj L : L →+* L).mapMatrix b)ᵀ

def zOf (b : Matrix (Fin n) (Fin n) L) : Fin n → Fin n → InfinitePlace L → ℂ :=
  fun i j w => w.embedding (b i j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[skewL, skewOf, zOf, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]`.
-/
theorem map_skewL (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (skewL b) = skewOf (zOf b) w := by
  ext i j
  simp [skewL, skewOf, zOf, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Introduce `h0`. Set `w0 : InfinitePlace L` to `Classical.arbitrary _`. Apply `det_one_add_ne_zero (skewOf_skew (zOf b) w0)` to reduce the goal to its premises. Rewrite using `[← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_add, det_mapMatrix, h0, map_zero]`.
-/
theorem det_one_add_skewL (b : Matrix (Fin n) (Fin n) L) : (1 + skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply det_one_add_ne_zero (skewOf_skew (zOf b) w0)
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_add, det_mapMatrix, h0, map_zero]

/- English proof (translation)
Introduce `h0`. Set `w0 : InfinitePlace L` to `Classical.arbitrary _`. Apply `(isUnit_det_one_sub (skewOf_skew (zOf b) w0)).ne_zero` to reduce the goal to its premises. Rewrite using `[← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_sub, det_mapMatrix, h0, map_zero]`.
-/
theorem det_one_sub_skewL (b : Matrix (Fin n) (Fin n) L) : (1 - skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply (isUnit_det_one_sub (skewOf_skew (zOf b) w0)).ne_zero
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_sub, det_mapMatrix, h0, map_zero]

/- English proof (translation)
Unfold `cay`. Rewrite using `[map_mul, mapMatrix_inv _ _ (det_one_add_skewL b), map_sub, map_add, map_one, map_skewL]`.
-/
theorem map_cay (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (cay (skewL b)) = cay (skewOf (zOf b) w) := by
  unfold cay
  rw [map_mul, mapMatrix_inv _ _ (det_one_add_skewL b), map_sub, map_add, map_one, map_skewL]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[conjT, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]`.
-/
theorem map_conjT (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) :
    f.mapMatrix (conjT (IsCMField.complexConj L : L →+* L) M) = (f.mapMatrix M)ᴴ := by
  ext i j
  simp [conjT, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Set `w0 : InfinitePlace L` to `Classical.arbitrary _`. Establish `hinj : Function.Injective (w0.embedding.mapMatrix : Matrix (Fin n) (Fin n) L →+* _)`. Introduce `M N h`. Use extensionality with `i j`. Conclude with `w0.embedding.injective (congrFun (congrFun h i) j)`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_conjT, map_cay, map_one]`. Conclude with `cay_mul_conjTranspose (skewOf_skew (zOf b) w0)`.
-/
theorem cay_skewL_mem (b : Matrix (Fin n) (Fin n) L) :
    cay (skewL b) * conjT (IsCMField.complexConj L : L →+* L) (cay (skewL b)) = 1 := by
  let w0 : InfinitePlace L := Classical.arbitrary _
  have hinj : Function.Injective (w0.embedding.mapMatrix : Matrix (Fin n) (Fin n) L →+* _) := by
    intro M N h
    ext i j
    exact w0.embedding.injective (congrFun (congrFun h i) j)
  apply hinj
  rw [map_mul, map_conjT, map_cay, map_one]
  exact cay_mul_conjTranspose (skewOf_skew (zOf b) w0)

/- English proof (translation)
Unfold `cay`. Rewrite using `[det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (det_one_sub_skewL b) (inv_ne_zero (det_one_add_skewL b))`.
-/
theorem det_cay_skewL (b : Matrix (Fin n) (Fin n) L) : (cay (skewL b)).det ≠ 0 := by
  unfold cay
  rw [det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (det_one_sub_skewL b) (inv_ne_zero (det_one_add_skewL b))

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨σ, i, j⟩` from `p`. Simplify using `only [ratPt, cpt]`. Use `split_ifs with h`. Rewrite using `[← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply] conv_rhs => rw [← h]`.

Establish `hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding`. Break down `InfinitePlace.embedding_mk_eq σ with h' | h'` into its components or cases. Conclude with `absurd h'.symm h`. Rewrite using `[h']`. Conclude with `(star_star σ).symm`.

Rewrite using `[← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `conv_lhs => rw [hc]`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Both sides reduce to the same expression.
-/
theorem ratPt_cay (b : Matrix (Fin n) (Fin n) L) :
    ratPt (cay (skewL b)) = cpt (fun w => cay (skewOf (zOf b) w)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [ratPt, cpt]
  split_ifs with h
  · rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_rhs => rw [← h]
  · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
      rcases InfinitePlace.embedding_mk_eq σ with h' | h'
      · exact absurd h'.symm h
      · rw [h']; exact (star_star σ).symm
    rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_lhs => rw [hc]
    rw [ComplexEmbedding.conjugate_coe_eq]
    rfl

/- English proof (translation)
Establish `hu : IsUnit (cay (skewL b))` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_cay_skewL b))`. Establish `hmem : hu.unit ∈ GQ0 L n` using `by show ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1`. Rewrite using `[IsUnit.unit_spec]`. Conclude with `cay_skewL_mem b`. Use `hF _ hmem` as an intermediate fact.

Rewrite `this` using `[IsUnit.unit_spec, ratPt_cay]`. Then use the resulting hypothesis.
-/
theorem rat_zero (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0)
    (b : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (cpt (fun w => cay (skewOf (zOf b) w))) F = 0 := by
  have hu : IsUnit (cay (skewL b)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_cay_skewL b))
  have hmem : hu.unit ∈ GQ0 L n := by
    show ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      conjT (IsCMField.complexConj L : L →+* L) ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1
    rw [IsUnit.unit_spec]
    exact cay_skewL_mem b
  have := hF _ hmem
  rwa [IsUnit.unit_spec, ratPt_cay] at this

/- English proof (translation)
Introduce `L _ _ _ n F hF Y hYu hY1`. Establish `hH : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => MvPolynomial.eval (cpt (fun w => cay (skewOf z w))) F) = fun _ => 0` using `(denseRange_matEmb (L := L) (n := n)).equalizer ((MvPolynomial.continuous_eval F).comp continuous_cpt_cay) continuous_const (funext fun b => rat_zero F hF b)`. Use `choose X hXs hXc using fun w => exists_cay (hYu w) (hY1 w)`. Set `z : Fin n → Fin n → InfinitePlace L → ℂ` to `fun i j w => ((2 : ℂ)⁻¹ • X w) i j`. Establish `hz : ∀ w, cay (skewOf z w) = Y w`.

Introduce `w`. Establish `hs : skewOf z w = X w`. Use extensionality with `i j`. Establish `h1` using `congrArg (fun M => M i j) (hXs w)`. Simplify using `only [conjTranspose_apply, Matrix.neg_apply] at h1`.

Establish `h2 : (starRingEnd ℂ) (X w j i) = -X w i j` using `h1`. Simplify using `only [skewOf, z, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul']`. Simplify using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, hXc]`.

Rewrite using `[repPt_eq_cpt Y hYu]`. Use `congrFun hH z` as an intermediate fact. Rewrite `this` using `[show (fun w => cay (skewOf z w)) = Y from funext hz]`. Then use the resulting hypothesis.
-/
theorem density_first_bound : DensA := by
  intro L _ _ _ n F hF Y hYu hY1
  have hH : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => MvPolynomial.eval (cpt (fun w => cay (skewOf z w))) F) =
      fun _ => 0 :=
    (denseRange_matEmb (L := L) (n := n)).equalizer ((MvPolynomial.continuous_eval F).comp continuous_cpt_cay)
      continuous_const (funext fun b => rat_zero F hF b)
  choose X hXs hXc using fun w => exists_cay (hYu w) (hY1 w)
  let z : Fin n → Fin n → InfinitePlace L → ℂ := fun i j w => ((2 : ℂ)⁻¹ • X w) i j
  have hz : ∀ w, cay (skewOf z w) = Y w := by
    intro w
    have hs : skewOf z w = X w := by
      ext i j
      have h1 := congrArg (fun M => M i j) (hXs w)
      simp only [conjTranspose_apply, Matrix.neg_apply] at h1
      have h2 : (starRingEnd ℂ) (X w j i) = -X w i j := h1
      simp only [skewOf, z, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul']
      simp [h2]
      ring
    rw [hs, hXc]
  rw [repPt_eq_cpt Y hYu]
  have := congrFun hH z
  rwa [show (fun w => cay (skewOf z w)) = Y from funext hz] at this

/- English proof (translation)
The claim follows from `densStep_of density_first_bound density_second_bound`.
-/
theorem density_induction : DensStep := densStep_of density_first_bound density_second_bound

end PI.UnitaryGroupMassFormula.HwConjInf
