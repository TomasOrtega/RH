import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyOfFrameValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionaryStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormOne

section An

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ A.X`. Establish `e : ((r, 0) : A.V) = ∑ i, (r (b i)).re • A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0)`. Use `Prod.ext (AddMonoidHom.ext fun x => ?_) ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_sum, AddMonoidHom.finset_sum_apply] conv_lhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, map_zsmul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : r (b i) = ((r (b i)).re : ℂ)` using `Complex.ext (by simp) (by simp [hr])`. Express the relevant statement in the definitionally equal form `_ = (r (b i)).re • (A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0)).1 x`. Rewrite using `[AnArc.Pw_fst_apply, Complex.real_smul, ← h1]`. Simplify using `[mul_comm]`.

Rewrite using `[Prod.snd_sum]`. Simplify using the standard rewrite rules. Rewrite using `[e, map_sum]`. Simplify using `[h]`.
-/
theorem map_real_eq_zero (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (h : ∀ n, φ (A.Pw w (AnArc.La.mk 0 n 0)) = 0)
    (r : A.X →+ ℂ) (hr : ∀ x, (r x).im = 0) : φ (r, 0) = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  have e : ((r, 0) : A.V) =
      ∑ i, (r (b i)).re • A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0) := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [Prod.fst_sum, AddMonoidHom.finset_sum_apply]
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : r (b i) = ((r (b i)).re : ℂ) := Complex.ext (by simp) (by simp [hr])
      change _ = (r (b i)).re • (A.Pw w (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0)).1 x
      rw [AnArc.Pw_fst_apply, Complex.real_smul, ← h1]
      simp [mul_comm]
    · rw [Prod.snd_sum]
      simp
  rw [e, map_sum]
  simp [h]

def abLift : (Fin A.gB → ℂ) →ₗ[ℝ] A.V where
  toFun z :=
    ({ toFun := fun x => -(A.H (A.ct x) z / (2 * Complex.I))
       map_zero' := by simp
       map_add' := fun x x' => by simp only [map_add, AnArc.H_add_left]; ring }, z)
  map_add' z z' := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) rfl
    change -(A.H (A.ct x) (z + z') / (2 * Complex.I)) =
      -(A.H (A.ct x) z / (2 * Complex.I)) + -(A.H (A.ct x) z' / (2 * Complex.I))
    rw [AnArc.H_add_right]; ring
  map_smul' t z := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) rfl
    change -(A.H (A.ct x) (t • z) / (2 * Complex.I)) = t • -(A.H (A.ct x) z / (2 * Complex.I))
    rw [← Complex.coe_smul, AnArc.H_smul_right, Complex.conj_ofReal, Complex.real_smul]; ring

/- English proof (translation)
Establish `e : φ ∘ₗ abLift A = 0`. Use `LinearMap.ext_on A.full fun m hm => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply, ← h ⟨m, hm⟩, LinearMap.comp_apply]`. Use `congr 1`. Use `Prod.ext (AddMonoidHom.ext fun x => ?_) (by simp [abLift])` and prove the remaining obligations.

Rewrite using `[AnArc.Pw_fst_apply]`. Simplify using `[abLift]`. Conclude with `LinearMap.congr_fun e z`.
-/
theorem map_abLift_eq_zero (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (h : ∀ m, φ (A.Pw w (AnArc.La.mk 0 0 m)) = 0)
    (z : Fin A.gB → ℂ) : φ (abLift A z) = 0 := by
  have e : φ ∘ₗ abLift A = 0 := by
    refine LinearMap.ext_on A.full fun m hm => ?_
    rw [LinearMap.zero_apply, ← h ⟨m, hm⟩, LinearMap.comp_apply]
    congr 1
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) (by simp [abLift])
    rw [AnArc.Pw_fst_apply]
    simp [abLift]
  exact LinearMap.congr_fun e z

/- English proof (translation)
Use `set u : A.V := A.Pw w (AnArc.La.mk v.y 0 0) - abLift A (A.ct v.y) - w.im • Complex.I • A.N v with hu`. Establish `h2 : u = (u.1, 0)` using `Prod.ext rfl (by simp [hu, abLift])`. Establish `h3 : φ u = 0`. Rewrite using `[h2]`. Use `map_real_eq_zero A φ w (fun n => by simp [h]) _ fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((A.Pw w (AnArc.La.mk v.y 0 0)).1 x - -(A.H (A.ct x) (A.ct v.y) / (2 * Complex.I)) - w.im • Complex.I • (A.N v).1 x).im = 0`. Establish `h4 : A.H (A.ct x) (A.ct v.y) / (2 * Complex.I) = -Complex.I * A.H (A.ct x) (A.ct v.y) / 2`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Establish `h5 : (A.H (A.ct x) (A.ct v.y)).re = (A.H (A.ct v.y) (A.ct x)).re`.

Rewrite using `[← A.H_conj, Complex.conj_re]`. Rewrite using `[h4, AnArc.Pw_fst_apply, AnArc.N_fst_apply]`. Simplify using `[hn, h5]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[hu, map_sub, map_sub, map_smul, h, map_abLift_eq_zero A φ w (fun m => by simp [h])]`.

Simplify using `only [AnArc.La.mk_y, smul_eq_mul] at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem map_I_smul_N (φ : A.V →ₗ[ℝ] ℝ) (w : ℂ) (v : A.La) (h : ∀ la, φ (A.Pw w la) = -(A.be v.y la.y : ℝ))
    (hn : ∀ x, (A.T v.y x).im = (A.H (A.ct v.y) (A.ct x)).re / 2) :
    φ (Complex.I • A.N v) * w.im = -(A.be v.y v.y : ℝ) := by
  set u : A.V := A.Pw w (AnArc.La.mk v.y 0 0) - abLift A (A.ct v.y) - w.im • Complex.I • A.N v with hu
  have h2 : u = (u.1, 0) := Prod.ext rfl (by simp [hu, abLift])
  have h3 : φ u = 0 := by
    rw [h2]
    refine map_real_eq_zero A φ w (fun n => by simp [h]) _ fun x => ?_
    change ((A.Pw w (AnArc.La.mk v.y 0 0)).1 x - -(A.H (A.ct x) (A.ct v.y) / (2 * Complex.I)) -
      w.im • Complex.I • (A.N v).1 x).im = 0
    have h4 : A.H (A.ct x) (A.ct v.y) / (2 * Complex.I) = -Complex.I * A.H (A.ct x) (A.ct v.y) / 2 := by
      field_simp
      simp
    have h5 : (A.H (A.ct x) (A.ct v.y)).re = (A.H (A.ct v.y) (A.ct x)).re := by
      rw [← A.H_conj, Complex.conj_re]
    rw [h4, AnArc.Pw_fst_apply, AnArc.N_fst_apply]
    simp [hn, h5]
    ring
  rw [hu, map_sub, map_sub, map_smul, h, map_abLift_eq_zero A φ w (fun m => by simp [h])] at h3
  simp only [AnArc.La.mk_y, smul_eq_mul] at h3
  linarith

/- English proof (translation)
Rewrite `h` using `[eTwoPi, ← Complex.exp_add]`. Establish `h1` using `congrArg norm h`. Rewrite `h1` using `[Complex.norm_exp, norm_one, Real.exp_eq_one_iff, ← Nat.cast_smul_eq_nsmul ℂ n (A.ct y), ← Nat.cast_smul_eq_nsmul ℂ n (A.ct x), AnArc.H_smul_left, AnArc.H_smul_right]`. Simplify using `only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at h1`. Simplify using `at h1`.

Establish `h2 : (Real.pi * n * n) * ((A.H (A.ct y) (A.ct x)).re - 2 * (A.T y x).im) = 0` using `by linarith`. Establish `h3 : (Real.pi * n * n) ≠ 0` using `by positivity`. Use `(mul_eq_zero.1 h2).resolve_left h3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem im_T_eq {n : ℕ} (hn : 0 < n) (y x : A.X)
    (h : eTwoPi (A.T (n • y) (n • x)) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct x)) = 1) :
    (A.T y x).im = (A.H (A.ct y) (A.ct x)).re / 2 := by
  rw [eTwoPi, ← Complex.exp_add] at h
  have h1 := congrArg norm h
  rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff, ← Nat.cast_smul_eq_nsmul ℂ n (A.ct y),
    ← Nat.cast_smul_eq_nsmul ℂ n (A.ct x), AnArc.H_smul_left, AnArc.H_smul_right] at h1
  simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at h1
  simp at h1
  have h2 : (Real.pi * n * n) * ((A.H (A.ct y) (A.ct x)).re - 2 * (A.T y x).im) = 0 := by linarith
  have h3 : (Real.pi * n * n) ≠ 0 := by positivity
  have := (mul_eq_zero.1 h2).resolve_left h3
  linarith

end An

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z₀ : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (hermForm Hm z₀ z).im
  map_add' z z' := by simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  map_smul' t z := by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[imForm, hermForm, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg]`.
-/
theorem imForm_I_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z₀ z : Fin g → ℂ) :
    imForm Hm z₀ (Complex.I • z) = -(hermForm Hm z₀ z).re := by
  simp [imForm, hermForm, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg]

/- English proof (translation)
Introduce `K E _ _ _ H Dw l Xo c _ _ σ O _ β Y a χ W g ty Fu Ha n hn htau w _ Hm hH v`. Use `letI := H.starRing`. Take `⟨Λ'⟩` from `GlobalTheory.ArcModel.nonempty_gtAn K.laws K.laws2 K.theta E H Dw l c O β _ a`. Take `⟨Λ''⟩` from `GlobalTheory.ArcDictModel.nonempty_of_frameValues Λ'`. Set `Λ` to `Λ''.toGtAn₀`.

Take `⟨gam, h, -, hy, hP, hE⟩` from `GlobalTheory.T.holomorphicArc_agrees_analyticDictionary K E H Dw l Xo c σ O β Y a χ W g ty Fu Ha Λ`. Establish `hN` using `((GlobalTheory.T.isTauCanonicalTrivialisation_iff_normalised_arc E H Dw l c O β _ a Λ n).1 htau).2`. Establish `hNv : h (Ha.N v) = Λ.A.N (gam v)`. Establish `h0` using `hP 0 v`. Establish `h1` using `hP 1 v`.

Rewrite `h0`, `h1` using `[Ha.Pw_eq, AnArc.Pw_apply]`. Simplify using `only [zero_smul, add_zero, one_smul, map_add] at h0 h1`. Rewrite `h1` using `[h0]`. Conclude with `add_left_cancel h1`. Establish `hNP : Ha.N v = Ha.Pw w (gam.symm (Λ.A.nn (gam v)))`.

Apply `h.injective` to reduce the goal to its premises. Rewrite using `[hNv, hP, LinearEquiv.apply_symm_apply, Λ.A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, AnArc.degeneratingTori_basePeriodMap_nilpotentMap]`. Establish `key` using `map_I_smul_N Λ.A (imForm Hm (Ha.N v) ∘ₗ (h.symm.toLinearMap.restrictScalars ℝ)) w (gam v) (fun la => by`. Take `⟨v', rfl⟩` from `gam.surjective la`. Express the relevant statement in the definitionally equal form `(hermForm Hm (Ha.N v) (h.symm (Λ.A.Pw w (gam v')))).im = _`.

Rewrite using `[← hP, LinearEquiv.symm_apply_apply, hNP, hH.2.2, ← hE, LinearEquiv.apply_symm_apply, AnArc.nn_apply, AnArc.EF_n_left]`. Use the proof step `simp)`. Use the proof step `(fun x => im_T_eq Λ.A hn _ _ (hN _ _))`. Express the relevant statement in the definitionally equal form `imForm Hm (Ha.N v) (h.symm (Complex.I • Λ.A.N (gam v))) * w.im = _ at key`. Rewrite `key` using `[← hNv, ← map_smul, LinearEquiv.symm_apply_apply, imForm_I_smul, ← Λ.be_eq, ← Λ.y_apply, hy]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem normOne_of_tauCan : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (n : ℕ), 0 < n → TauCan a.D₀ n → NormOne Ha := by
  intro K E _ _ _ H Dw l Xo c _ _ σ O _ β Y a χ W g ty Fu Ha n hn htau w _ Hm hH v
  letI := H.starRing
  obtain ⟨Λ'⟩ := GlobalTheory.ArcModel.nonempty_gtAn K.laws K.laws2 K.theta E H Dw l c O β _ a
  obtain ⟨Λ''⟩ := GlobalTheory.ArcDictModel.nonempty_of_frameValues Λ'
  let Λ := Λ''.toGtAn₀
  obtain ⟨gam, h, -, hy, hP, hE⟩ := GlobalTheory.T.holomorphicArc_agrees_analyticDictionary K E H Dw l Xo c σ O β Y a χ W g ty Fu Ha Λ
  have hN := ((GlobalTheory.T.isTauCanonicalTrivialisation_iff_normalised_arc E H Dw l c O β _ a Λ n).1 htau).2
  have hNv : h (Ha.N v) = Λ.A.N (gam v) := by
    have h0 := hP 0 v
    have h1 := hP 1 v
    rw [Ha.Pw_eq, AnArc.Pw_apply] at h0 h1
    simp only [zero_smul, add_zero, one_smul, map_add] at h0 h1
    rw [h0] at h1
    exact add_left_cancel h1
  have hNP : Ha.N v = Ha.Pw w (gam.symm (Λ.A.nn (gam v))) := by
    apply h.injective
    rw [hNv, hP, LinearEquiv.apply_symm_apply, Λ.A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, AnArc.degeneratingTori_basePeriodMap_nilpotentMap]
  have key := map_I_smul_N Λ.A (imForm Hm (Ha.N v) ∘ₗ (h.symm.toLinearMap.restrictScalars ℝ)) w (gam v)
    (fun la => by
      obtain ⟨v', rfl⟩ := gam.surjective la
      change (hermForm Hm (Ha.N v) (h.symm (Λ.A.Pw w (gam v')))).im = _
      rw [← hP, LinearEquiv.symm_apply_apply, hNP, hH.2.2, ← hE, LinearEquiv.apply_symm_apply, AnArc.nn_apply,
        AnArc.EF_n_left]
      simp)
    (fun x => im_T_eq Λ.A hn _ _ (hN _ _))
  change imForm Hm (Ha.N v) (h.symm (Complex.I • Λ.A.N (gam v))) * w.im = _ at key
  rw [← hNv, ← map_smul, LinearEquiv.symm_apply_apply, imForm_I_smul, ← Λ.be_eq, ← Λ.y_apply, hy] at key
  linarith

end GlobalTheory.ArcNormOne
