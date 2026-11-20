import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def detProd (p : HV E a) : ℝ := ∏ w : InfinitePlace E, ((Matrix.of p.1).det w).re

/- English proof (translation)
Unfold `detProd`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[sand_val, det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm]`. Establish `h : (g.val.det * star g.val.det * (Matrix.of p.1).det) w = ((‖g.val.det w‖ ^ 2 : ℝ) : ℂ) * (Matrix.of p.1).det w`.

Rewrite using `[Pi.mul_apply, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[h, Complex.re_ofReal_mul]`.
-/
private theorem detProd_sand (g : GL (Fin a) (Cinf E)) (p : HV E a) :
    detProd (sand g p) = (∏ w : InfinitePlace E, ‖g.val.det w‖ ^ 2) * detProd p := by
  unfold detProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [sand_val, det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm]
  have h : (g.val.det * star g.val.det * (Matrix.of p.1).det) w =
      ((‖g.val.det w‖ ^ 2 : ℝ) : ℂ) * (Matrix.of p.1).det w := by
    rw [Pi.mul_apply, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.re_ofReal_mul]

/- English proof (translation)
Unfold `detProd`. Use `contDiff_prod fun w _ => Complex.reCLM.contDiff.comp (f := fun p : HV E a => (Matrix.of p.1).det w) ?_` and prove the remaining obligations. Simplify using `only [det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, of_apply]`. Use `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)` and prove the remaining obligations. Establish `h : ContDiff ℝ ∞ (fun p : HV E a => p.1)` using `(HV E a).subtypeL.contDiff`.

Conclude with `contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 h _) _) _`.
-/
private theorem contDiff_detProd : ContDiff ℝ ∞ (detProd (E := E) (a := a)) := by
  unfold detProd
  refine contDiff_prod fun w _ => Complex.reCLM.contDiff.comp (f := fun p : HV E a => (Matrix.of p.1).det w) ?_
  simp only [det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  have h : ContDiff ℝ ∞ (fun p : HV E a => p.1) := (HV E a).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 h _) _) _

/- English proof (translation)
Unfold `detProd`. Establish `h : ∀ w : InfinitePlace E, ((Matrix.of (t • p).1).det w).re = t ^ a * ((Matrix.of p.1).det w).re`. Introduce `w`. Establish `h1 : Matrix.of (t • p).1 = (algebraMap ℝ (Cinf E) t) • Matrix.of p.1`. Rewrite using `[algebraMap_smul]`.

Both sides reduce to the same expression. Rewrite using `[h1, det_smul, Fintype.card_fin, ← map_pow, ← Algebra.smul_def, Pi.smul_apply, Complex.smul_re, smul_eq_mul]`. Simplify using `only [h]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul]`.
-/
private theorem detProd_smul (t : ℝ) (p : HV E a) :
    detProd (t • p) = t ^ (a * Fintype.card (InfinitePlace E)) * detProd p := by
  unfold detProd
  have h : ∀ w : InfinitePlace E, ((Matrix.of (t • p).1).det w).re = t ^ a * ((Matrix.of p.1).det w).re := by
    intro w
    have h1 : Matrix.of (t • p).1 = (algebraMap ℝ (Cinf E) t) • Matrix.of p.1 := by
      rw [algebraMap_smul]; rfl
    rw [h1, det_smul, Fintype.card_fin, ← map_pow, ← Algebra.smul_def, Pi.smul_apply, Complex.smul_re, smul_eq_mul]
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul]

/- English proof (translation)
Introduce `E _ _ _ a`. Use `⟨detProd, contDiff_detProd, ?_, detProd_smul, ?_⟩` and prove the remaining obligations. Introduce and unpack `p ⟨g, rfl⟩`. Rewrite using `[detProd_sand]`. Establish `h1 : detProd (hOne E a) = 1`.

Unfold `detProd`. Rewrite using `[hOne_val, det_one]`. Simplify using the standard rewrite rules. Rewrite using `[h1, mul_one]`. Use `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2` and prove the remaining obligations.

Establish `hu : IsUnit g.val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`. Conclude with `(hu.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero`. Introduce `γ p`. Rewrite using `[detProd_sand]`. Use `congr 1`.

Establish `hd : (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val.det = pInf E (algebraMap E (Ad E) γ.val.det)`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hd, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[pInf_algebraMap, InfinitePlace.norm_embedding_eq, IsTotallyComplex.mult_eq]`.
-/
theorem normInf : NormInf := by
  intro E _ _ _ a
  refine ⟨detProd, contDiff_detProd, ?_, detProd_smul, ?_⟩
  · rintro p ⟨g, rfl⟩
    rw [detProd_sand]
    have h1 : detProd (hOne E a) = 1 := by
      unfold detProd
      rw [hOne_val, det_one]
      simp
    rw [h1, mul_one]
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact (hu.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero
  · intro γ p
    rw [detProd_sand]
    congr 1
    have hd : (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val.det = pInf E (algebraMap E (Ad E) γ.val.det) := by
      rw [RingHom.map_det, RingHom.map_det]
      rfl
    rw [hd, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq, IsTotallyComplex.mult_eq]

end UpperTheory.V.Lit.Dr
