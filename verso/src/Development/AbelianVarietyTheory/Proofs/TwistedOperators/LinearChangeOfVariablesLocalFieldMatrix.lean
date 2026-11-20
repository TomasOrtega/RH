import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

/- English proof (translation)
Use `symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]`. Establish `hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s = Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j)`. Use extensionality with `x`.

Simplify using `[MeasurableEquiv.coe_curry_symm, Prod.forall]`. Rewrite using `[hpre, Measure.pi_pi]`. Repeatedly rewrite using `[Measure.pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`.
-/
theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Use `show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)`. Conclude with `NNReal.coe_pos.mpr distribHaarChar_pos`.
-/
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Conclude with `(Continuous.matrix_mulVec continuous_const continuous_id).measurable`.
-/
private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Establish `hD : ∀ i, D i ≠ 0`. Introduce `i hi`. Establish `h0 : (u : k) ≠ 0` using `u.ne_zero`. Rewrite `h0` using `[hu, Matrix.det_diagonal]`.

Conclude with `h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)`. Set `e : a → kˣ` to `fun i => Units.mk0 (D i) (hD i)`. Establish `hue : u = ∏ i, e i`. Use `ext`. Rewrite using `[hu, Matrix.det_diagonal, Units.coe_prod]`.

Both sides reduce to the same expression. Establish `hm` using `measurable_mulVec' (Matrix.diagonal D)`. Establish `E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν`. Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]`.

Establish `hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s = Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i`. Use extensionality with `x`. Simplify using `[Matrix.mulVec_diagonal, Units.smul_def, e]`. Rewrite using `[hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul, inv_mul_cancel, map_one, one_smul]`. Use `_ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]`.
-/
private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]

/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Take `⟨i, j, hij, c⟩` from `t`. Use `show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν`. Establish `hm` using `measurable_mulVec' (Matrix.transvection i j c)`. Establish `key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) = Function.update x i (y + c * x j)`.

Introduce `x y`. Use extensionality with `l`. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality. Simplify using `[Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]`.

Simplify using `[Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]`. Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Establish `hbox : MeasurableSet (Set.univ.pi s)` using `MeasurableSet.univ_pi hs`. Establish `hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal))` using `measurable_one.indicator hbox`. Rewrite using `[← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox, lintegral_map hind hm]`.

Use `lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[lmarginal_singleton, lmarginal_singleton]`. Simplify using `only [Function.comp_apply, key]`. Conclude with `lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)`.
-/
private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)

/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Use `revert u`. Use `Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ u : kˣ, (u : k) = M.det → Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν) M hM ?_ ?_ ?_` and prove the remaining obligations. Introduce `D _ u hu`. Conclude with `map_diagonal_mulVec_measure_pi ν D u hu`.

Introduce `t u hu`. Establish `h1 : u = 1` using `Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])`. Rewrite using `[h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]`. Introduce `A B hA hB IA IB u hu`. Establish `hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec`.

Use function extensionality and compare the values at `x`. Simplify using `[Matrix.mulVec_mulVec]`. Establish `hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹`. Rewrite using `[← mul_inv]`. Use `congr 1`.

Use `ext`. Simplify using `[hu, Matrix.det_mul, mul_comm]`. Rewrite using `[hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl, Measure.map_smul, IA (Units.mk0 _ hA) rfl, hinv, map_mul, mul_smul]`.
-/
private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul, IA (Units.mk0 _ hA) rfl, hinv, map_mul, mul_smul]

/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Establish `hdet : IsUnit M.det` using `isUnit_iff_ne_zero.mpr hM`. Set `e : (a → k) ≃ᵐ (a → k)` to `{ toFun := M.mulVec invFun := M⁻¹.mulVec left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet] right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] measurable_toFun := measurable_mulVec' M measurable_invFun := measurable …`. Establish `h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) = ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν))` using `(e.measurableEmbedding.integral_map f).symm`. Establish `h2 : (e : (a → k) → (a → k)) = M.mulVec` using `rfl`.

Rewrite using `[h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def, NNReal.coe_inv]`. Both sides reduce to the same expression.
-/
private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl

/- English proof (translation)
Conclude with `integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f`.
-/
theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
/- English proof (translation)
Establish `: SecondCountableTopology k` using `secondCountable k`. Rewrite using `[← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]`. Both sides reduce to the same expression.
-/
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Establish `hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0`. Rewrite using `[Matrix.det_kronecker, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero) (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)`. Use `set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a * Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def`. Establish `hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det`.

Rewrite using `[Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression. Rewrite using `[integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]`. Simplify using `only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]`. Rewrite using `[integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]`.

Use `congr 1`. Establish `hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a * nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b`. Simplify using `only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]`. Rewrite using `[hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast, Real.rpow_natCast]`.
-/
theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

/- English proof (translation)
Introduce `k _ _ _ _ _ _ a b _ _ _ _ ν _`. Conclude with `⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩`.
-/
theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
