import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightFunctionLemmas

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nF_eq (s : Fin 2 → F) (x : GF F) :
    nF s x = ∏ᶠ w : Pl F, max ‖pLoc F w (rowF s x 0)‖ ‖pLoc F w (rowF s x 1)‖ := rfl

/- English proof (translation)
Unfold `rowF`. Establish `h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) = (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i`. Rewrite using `[h, Units.val_mul, Matrix.vecMul_vecMul]`.
-/
theorem rowF_jF (s : Fin 2 → F) (γ : GL (Fin 2) F) (x : GF F) :
    rowF s (jF F γ * x) = rowF (s ᵥ* γ.val) x := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) =
      (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val := by
    funext i
    exact RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i
  rw [h, Units.val_mul, Matrix.vecMul_vecMul]

/- English proof (translation)
Unfold `rowF`. Establish `h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i))`. Use function extensionality and compare the values at `i`. Simplify using `[map_mul]`. Rewrite using `[h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]`.
-/
theorem rowF_smul (s : Fin 2 → F) (a : F) (x : GF F) (i : Fin 2) :
    rowF (a • s) x i = algebraMap F (Af F) a * rowF s x i := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i)) := by
    funext i
    simp [map_mul]
  rw [h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det`. Conclude with `(RingHom.map_det (algebraMap F (Af F)) γ.val).symm`.
-/
theorem det_jF (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F γ) = ratU F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  change (γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det
  exact (RingHom.map_det (algebraMap F (Af F)) γ.val).symm

variable [IsTotallyReal F]

/- English proof (translation)
Take `⟨t, k, hk, h⟩` from `(hR F s x).1 hs`. Rewrite using `[(hR F s x).2 t k hk h]`. Conclude with `(Hm.absf F).1 t`.
-/
theorem nF_pos (hR : ARow) {s : Fin 2 → F} (hs : s ≠ 0) (x : GF F) : 0 < nF s x := by
  obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
  rw [(hR F s x).2 t k hk h]
  exact (Hm.absf F).1 t

/- English proof (translation)
Unfold `reAt`. Rewrite using `[← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]`.
-/
theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

/- English proof (translation)
Use `(Hm.absf F).2.2.2 a` as an intermediate fact. Simplify using `only [reAt_eq] at this`. Conclude with `this`.
-/
theorem prod_rat (a : Fˣ) : (∏ v, |sg v (a : F)|) * absF (ratU F a) = 1 := by
  have := (Hm.absf F).2.2.2 a
  simp only [reAt_eq] at this
  exact this

end UpperTheory.Esk.HeightFunctionLemmas

open UpperTheory.Esk.HeightFunctionLemmas in
/- English proof (translation)
Introduce `hR F _ _ _ c _ χ`. Use `⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2`. Conclude with `div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)`. Express the relevant statement in the definitionally equal form `absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| = absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2`.

Establish `hP` using `prod_rat (Matrix.GeneralLinearGroup.det γ)`. Rewrite `hP` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]`. Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 = absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2`.

Take `⟨t, k, hk, h⟩` from `(hR F s x).1 hs`. Establish `h1` using `(hR F s x).2 t k hk h`. Establish `h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x`. Rewrite using `[(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by`. Rewrite using `[rowF_smul, h i, Units.val_mul, mul_assoc]`.

Use the proof step `rfl), (Hm.absf F).2.1, h1]`. Establish `hP` using `prod_rat (Units.mk0 a ha)`. Simplify using `only [Units.val_mk0] at hP`. Establish `hA` using `(Hm.absf F).1 (ratU F (Units.mk0 a ha))`. Establish `hN` using `nF_pos hR hs x`.

Establish `hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2`. Rewrite using `[← Finset.prod_pow]`. Simplify using `[sq_abs]`. Rewrite using `[h2, hsq, eq_inv_of_mul_eq_one_left hP]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.Esk.dHt : UpperTheory.Esk.ARow → UpperTheory.Esk.DHt := by
  intro hR F _ _ _ c _ χ
  refine ⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩
  · change 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
    exact div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)
  · change absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| =
      absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2
    have hP := prod_rat (Matrix.GeneralLinearGroup.det γ)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hP
    rw [map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]
    calc absF (ratU F (Matrix.GeneralLinearGroup.det γ)) * absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2 *
          ∏ v, |sg v γ.val.det|
        = ((∏ v, |sg v γ.val.det|) * absF (ratU F (Matrix.GeneralLinearGroup.det γ))) *
          (absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2) := by ring
      _ = _ := by rw [hP, one_mul]
  · change absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2
    obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
    have h1 := (hR F s x).2 t k hk h
    have h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x := by
      rw [(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by
        rw [rowF_smul, h i, Units.val_mul, mul_assoc]; rfl), (Hm.absf F).2.1, h1]
    have hP := prod_rat (Units.mk0 a ha)
    simp only [Units.val_mk0] at hP
    have hA := (Hm.absf F).1 (ratU F (Units.mk0 a ha))
    have hN := nF_pos hR hs x
    have hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [h2, hsq, eq_inv_of_mul_eq_one_left hP]
    field_simp
