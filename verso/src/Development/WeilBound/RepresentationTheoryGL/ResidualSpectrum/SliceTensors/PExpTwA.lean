import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ExponentTwist

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Rewrite using `[IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_places : ((Module.finrank ℚ E : ℕ) : ℂ) = 2 * (Fintype.card (InfinitePlace E) : ℂ) := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  push_cast; ring

omit [IsTotallyComplex E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chiDet_absC_val (a : ℕ) (s : ℂ) (g : GA E a) :
    ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) =
      Complex.exp (s * (GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) : ℂ)) := rfl

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => if i < r then t else 0), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Use `congr 2`. Rewrite using `[show Finset.filter (fun x => x < r) (Finset.range N) = Finset.range r by ext x; simp; omega]`. Simplify using the standard rewrite rules.
-/
theorem sum_ite_lt {N r : ℕ} (h : r ≤ N) (t : ℂ) :
    ∑ i : Fin N, (if (i : ℕ) < r then t else 0) = r * t := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then t else 0), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [show Finset.filter (fun x => x < r) (Finset.range N) = Finset.range r by ext x; simp; omega]
  simp

/- English proof (translation)
Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal fun (i : Fin N) (_ : InfinitePlace E) => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)).det w = _`. Rewrite using `[Matrix.det_diagonal, Finset.prod_apply, ← Complex.exp_sum, sum_ite_lt h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem det_aInf_apply {N r : ℕ} (h : r ≤ N) (t : ℝ) (w : InfinitePlace E) :
    ((Matrix.GeneralLinearGroup.det (aInf E N r t) : (Cinf E)ˣ) : Cinf E) w = Complex.exp ((r * t : ℝ) : ℂ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.diagonal fun (i : Fin N) (_ : InfinitePlace E) => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)).det w = _
  rw [Matrix.det_diagonal, Finset.prod_apply, ← Complex.exp_sum, sum_ite_lt h]
  push_cast; rfl

/- English proof (translation)
Rewrite using `[chiDet_absC_val, aT, det_infGL, Model.logNorm_infId]`. Simplify using `only [det_aInf_apply h, Complex.norm_exp_ofReal, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[card_places]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chiDet_aT {N r : ℕ} (h : r ≤ N) (z : ℂ) (t : ℝ) :
    ((chiDet N (Model.absC E z) (aT E N r t) : ℂˣ) : ℂ) = Complex.exp (z * r * (Module.finrank ℚ E : ℂ) * t) := by
  rw [chiDet_absC_val, aT, det_infGL, Model.logNorm_infId]
  simp only [det_aInf_apply h, Complex.norm_exp_ofReal, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_places]
  congr 1
  push_cast; ring

/- English proof (translation)
Use `congrArg (infGL E a) (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.scalar (Fin a) (expU fun _ : InfinitePlace E => (t : ℂ)).val = Matrix.diagonal _`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, expU]`.
-/
theorem splitCentre_eq (a : ℕ) (t : ℝ) : splitCentre E a t = aT E a a t := by
  refine congrArg (infGL E a) (Units.ext ?_)
  change Matrix.scalar (Fin a) (expU fun _ : InfinitePlace E => (t : ℂ)).val = Matrix.diagonal _
  ext i j
  simp [Matrix.scalar_apply, expU]

end PositivityTheory.Rg.Rs.ExponentTwist
