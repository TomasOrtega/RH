import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace OrbitChartMax

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def dehomCoords {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → Ω :=
  fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p

/- English proof (translation)
Use `conv_lhs => rw [G.as_sum]`. Use `conv_rhs => rw [G.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Establish `hmb : ∀ k, ∑ i, m ⟨k, i⟩ = b k` using `fun k ↦ by`.

Rewrite using `[← weight_coordDeg_apply, hG (mem_support_iff.mp hm)]`. Rewrite using `[aeval_monomial, aeval_monomial, mul_assoc]`. Use `congr 1`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]`. Repeatedly rewrite using `[mul_pow]`.

Rewrite using `[Finset.prod_mul_distrib, mul_comm]`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← hmb k]`.

Conclude with `Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (t k)`.
-/
theorem aeval_mul_of_homog {R : Type*} [CommRing R] [Algebra ℤ R] (t : ι → R) (z : Coord n → R)
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (fun p ↦ t p.1 * z p) G = aeval z G * ∏ k, t k ^ b k := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmb : ∀ k, ∑ i, m ⟨k, i⟩ = b k := fun k ↦ by
    rw [← weight_coordDeg_apply, hG (mem_support_iff.mp hm)]
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hmb k]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (t k)

def homDeg (F : MvPolynomial (Coord n) ℤ) : ι → ℕ :=
  fun k ↦ F.support.sup fun m ↦ Finsupp.weight (coordDeg n) m k

def homogenize (c : (k : ι) → Fin (n k + 1)) (F : MvPolynomial (Coord n) ℤ) :
    MvPolynomial (Coord n) ℤ :=
  ∑ m ∈ F.support, monomial m (coeff m F) *
    chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m)

/- English proof (translation)
Use `IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_` and prove the remaining obligations. Establish `hle : Finsupp.weight (coordDeg n) m ≤ homDeg F` using `fun k ↦ Finset.le_sup (f := fun m ↦ Finsupp.weight (coordDeg n) m k) hm`. Establish `h` using `(isWeightedHomogeneous_monomial (coordDeg n) m (coeff m F) rfl).mul (isWeightedHomogeneous_chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m))`. Rewrite `h` using `[add_tsub_cancel_of_le hle]`. Then use the resulting hypothesis.
-/
theorem isWeightedHomogeneous_homogenize (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (homogenize c F) (homDeg F) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hle : Finsupp.weight (coordDeg n) m ≤ homDeg F := fun k ↦
    Finset.le_sup (f := fun m ↦ Finsupp.weight (coordDeg n) m k) hm
  have h := (isWeightedHomogeneous_monomial (coordDeg n) m (coeff m F) rfl).mul
    (isWeightedHomogeneous_chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m))
  rwa [add_tsub_cancel_of_le hle] at h

/- English proof (translation)
Use `conv_rhs => rw [F.as_sum]`. Simplify using `only [homogenize, map_sum, map_mul, chartMonomial, map_prod, map_pow, hφ, one_pow, Finset.prod_const_one, mul_one]`.
-/
theorem map_homogenize {R : Type*} [CommRing R] (c : (k : ι) → Fin (n k + 1))
    (φ : MvPolynomial (Coord n) ℤ →+* R) (hφ : ∀ k, φ (X ⟨k, c k⟩) = 1)
    (F : MvPolynomial (Coord n) ℤ) : φ (homogenize c F) = φ F := by
  conv_rhs => rw [F.as_sum]
  simp only [homogenize, map_sum, map_mul, chartMonomial, map_prod, map_pow, hφ, one_pow,
    Finset.prod_const_one, mul_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(aeval (dehomCoords z c)).toRingHom F = _`. Rewrite using `[← map_homogenize c (aeval (dehomCoords z c)).toRingHom (fun k ↦ by`. Simplify using `[dehomCoords, inv_mul_cancel₀ (hz k)]) F]`. Conclude with `aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z (isWeightedHomogeneous_homogenize c F)`.
-/
theorem aeval_dehomCoords {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    aeval (dehomCoords z c) F =
      aeval z (homogenize c F) * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ homDeg F k := by
  change (aeval (dehomCoords z c)).toRingHom F = _
  rw [← map_homogenize c (aeval (dehomCoords z c)).toRingHom (fun k ↦ by
    simp [dehomCoords, inv_mul_cancel₀ (hz k)]) F]
  exact aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z (isWeightedHomogeneous_homogenize c F)

omit [DecidableEq ι] in

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (inv_ne_zero (hz k))`.
-/
theorem prod_inv_pow_ne_zero {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (D : ι → ℕ) : ∏ k, (z ⟨k, c k⟩)⁻¹ ^ D k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (inv_ne_zero (hz k))

/- English proof (translation)
Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap]`. Establish `e : (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) = fun p ↦ (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) * C (flatCone x p)`. Use function extensionality and compare the values at `fun p ↦ mul_comm _ _`. Establish `hC : aeval (fun p : Coord n ↦ (C (flatCone x p) : MvPolynomial ι (AlgebraicClosure ℚ))) G = C (aeval (flatCone x) G)`. Rewrite using `[aeval_def, aeval_def, eval₂_comp_left]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `aeval (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) G = 0`. Establish `h` using `aeval_mul_of_homog (fun k : ι ↦ (X k : MvPolynomial ι (AlgebraicClosure ℚ))) (fun p ↦ C (flatCone x p)) hG`. Use `beta_reduce at h`. Rewrite using `[e]`.

Use `h.trans (mul_eq_zero_of_left (hC.trans ?_) _)` and prove the remaining obligations. Rewrite using `[h0, map_zero]`.
-/
theorem mem_orbitIdeal_of_aeval_eq_zero (x : Cone n (AlgebraicClosure ℚ))
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b)
    (h0 : aeval (flatCone x) G = 0) : G ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap]
  have e : (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) =
      fun p ↦ (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) * C (flatCone x p) :=
    funext fun p ↦ mul_comm _ _
  have hC : aeval (fun p : Coord n ↦ (C (flatCone x p) : MvPolynomial ι (AlgebraicClosure ℚ))) G =
      C (aeval (flatCone x) G) := by
    rw [aeval_def, aeval_def, eval₂_comp_left]
    congr 1
  change aeval (fun p : Coord n ↦ C (flatCone x p) * (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ))) G = 0
  have h := aeval_mul_of_homog (fun k : ι ↦ (X k : MvPolynomial ι (AlgebraicClosure ℚ)))
    (fun p ↦ C (flatCone x p)) hG
  beta_reduce at h
  rw [e]
  refine h.trans (mul_eq_zero_of_left (hC.trans ?_) _)
  rw [h0, map_zero]

/- English proof (translation)
The claim follows from `aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z hG`.
-/
theorem aeval_dehomCoords_of_homog {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω)
    (c : (k : ι) → Fin (n k + 1)) {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ}
    (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (dehomCoords z c) G = aeval z G * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ b k :=
  aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z hG

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
The claim follows from `MvPolynomial.algHom_ext fun _ ↦ by simp [chartEval]`.
-/
theorem val_comp_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
  MvPolynomial.algHom_ext fun _ ↦ by simp [chartEval]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Introduce and unpack `⟨u, hu⟩`. Establish `hu'` using `hu`. Rewrite `hu'` using `[chartRing, Algebra.adjoin_range_eq_range_aeval]`. Take `⟨F, hF⟩` from `hu'`. Conclude with `⟨F, Subtype.ext ((DFunLike.congr_fun (val_comp_chartEval x c) F).trans hF)⟩`.
-/
theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨u, hu⟩
  have hu' := hu
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at hu'
  obtain ⟨F, hF⟩ := hu'
  exact ⟨F, Subtype.ext ((DFunLike.congr_fun (val_comp_chartEval x c) F).trans hF)⟩

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq, map_add]`. Consider the case `mul_X p q hp`. Rewrite using `[map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp, map_mul]`.

Simplify using `[chartEval, chartRatio, dehomCoords, flatCone, div_eq_inv_mul]`.
-/
theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c F : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (dehomCoords (flatCone x) c) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq, map_add]
  | mul_X p q hp =>
    rw [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp, map_mul]
    simp [chartEval, chartRatio, dehomCoords, flatCone, div_eq_inv_mul]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Rewrite using `[← coe_chartEval, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero]`.
-/
theorem chartEval_eq_zero_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    chartEval x c F = 0 ↔ aeval (dehomCoords (flatCone x) c) F = 0 := by
  rw [← coe_chartEval, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_chartEval]`. Simplify using `[dehomCoords, inv_mul_cancel₀ (hxc k)]`.
-/
theorem chartEval_X_chart (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0) (k : ι) : chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_chartEval]
  simp [dehomCoords, inv_mul_cancel₀ (hxc k)]

section Generic

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

omit [Fintype ι] [DecidableEq ι] in

def genPt : Coord n → FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  fun p ↦ algebraMap _ _ (Ideal.Quotient.mk V (X p))

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

/- English proof (translation)
Establish `h : (aeval (genPt V)).toRingHom = (algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp (Ideal.Quotient.mk V)` using `MvPolynomial.ringHom_ext (fun a ↦ RingHom.congr_fun (RingHom.ext_int ((aeval (genPt V)).toRingHom.comp C) (((algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp (Ideal.Quotient.mk V)).comp C)) a) (fun p ↦ by simp [genPt])`. Conclude with `DFunLike.congr_fun h F`.
-/
theorem aeval_genPt (F : MvPolynomial (Coord n) ℤ) :
    aeval (genPt V) F = algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))
      (Ideal.Quotient.mk V F) := by
  have h : (aeval (genPt V)).toRingHom =
      (algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp (Ideal.Quotient.mk V) :=
    MvPolynomial.ringHom_ext (fun a ↦ RingHom.congr_fun (RingHom.ext_int
      ((aeval (genPt V)).toRingHom.comp C)
      (((algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))).comp
        (Ideal.Quotient.mk V)).comp C)) a)
      (fun p ↦ by simp [genPt])
  exact DFunLike.congr_fun h F

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

/- English proof (translation)
Rewrite using `[aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem aeval_genPt_eq_zero_iff (F : MvPolynomial (Coord n) ℤ) : aeval (genPt V) F = 0 ↔ F ∈ V := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in

/- English proof (translation)
Establish `h` using `(aeval_genPt_eq_zero_iff V (X p)).not.mpr hp`. Rewrite `h` using `[aeval_X]`. Then use the resulting hypothesis.
-/
theorem genPt_ne_zero {p : Coord n} (hp : (X p : MvPolynomial (Coord n) ℤ) ∉ V) : genPt V p ≠ 0 := by
  have h := (aeval_genPt_eq_zero_iff V (X p)).not.mpr hp
  rwa [aeval_X] at h

end Generic

/- English proof (translation)
Introduce `ι _ _ _ n A x s hx hs V hV c hc`. Take `⟨hVmin, -⟩` from `hV`. Establish `: V.IsPrime` using `hVmin.1.1`. Establish `hPV : orbitIdeal x ≤ V` using `le_sup_left.trans hVmin.1.2`. Establish `hsV : s ∈ V` using `hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`.

Take `⟨a, -, hsa, hsP⟩` from `hs`. Establish `hsa' : IsWeightedHomogeneous (coordDeg n) s a` using `(geoMultiHomog_iff s a).mp hsa`. Establish `hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V`. Establish `hJ : NumbersDVR.IsMultiHomogIdeal (ι` using `blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by`. Introduce `f hf b`.

Take `⟨p, hp, t, ht, rfl⟩` from `Submodule.mem_sup.mp hf`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b) (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)`. Conclude with `NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin`. Establish `hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0`.

Introduce `k h0`. Use `hc k (hPV ?_)` and prove the remaining obligations. Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]`. Simplify using `[h0]`. Establish `hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0` using `fun k ↦ genPt_ne_zero V (hc k)`.

Establish `hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0`. Introduce `f hf`. Rewrite using `[← sum_weightedHomogeneousComponent (w := coordDeg n) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]`. Use `Finset.sum_eq_zero fun b _ ↦ ?_` and prove the remaining obligations. Conclude with `(aeval_dehomCoords_of_homog (genPt V) c (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)`.

Establish `hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0`. Introduce `F hF`. Rewrite `hF` using `[chartEval_eq_zero_iff]`. Establish `hF'` using `(aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF`. Establish `hH` using `(mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)`.

Establish `hHV : homogenize c F ∈ V` using `hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)`. Conclude with `(aeval_dehomCoords (genPt V) c hyc F).trans (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)`. Establish `hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔ aeval (dehomCoords (genPt V) c) F = 0`. Introduce `F`. Prove the components needed by the constructor for the conclusion.

Introduce `hF`. Take `⟨v, hv, hvF⟩` from `(Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF`. Establish `h1` using `hker (F - v) (by rw [map_sub, hvF, sub_self])`. Rewrite `h1` using `[map_sub, hVzero v hv, sub_zero]`. Then use the resulting hypothesis. Introduce `hF`.

Establish `hF'` using `(aeval_dehomCoords (genPt V) c hyc F).symm.trans hF`. Establish `hH` using `(aeval_genPt_eq_zero_iff V _).mp ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))`. Establish `e : chartEval x c (homogenize c F) = chartEval x c F` using `map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F`. Rewrite using `[← e]`. Conclude with `Ideal.mem_map_of_mem _ hH`.

Establish `hprime : (chartPoint x c V).IsPrime`. Use `⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩` and prove the remaining obligations. Establish `h1 : chartEval x c 1 ∈ chartPoint x c V` using `by rw [htop]; exact Submodule.mem_top`. Rewrite `h1` using `[hmem, map_one]`. Conclude with `one_ne_zero h1`.

Take `⟨F, rfl⟩` from `chartEval_surjective x c u`. Take `⟨G, rfl⟩` from `chartEval_surjective x c v`. Rewrite `huv` using `[← map_mul, hmem, map_mul]`. Break down `mul_eq_zero.mp huv with h | h` into its components or cases. Conclude with `Or.inl ((hmem F).mpr h)`.

Conclude with `Or.inr ((hmem G).mpr h)`. Establish `hne : chartPoint x c V ≠ ⊥`. Introduce `hbot`. Establish `h1 : chartEval x c s ∈ chartPoint x c V` using `Ideal.mem_map_of_mem _ hsV`. Rewrite `h1` using `[hbot, Ideal.mem_bot, chartEval_eq_zero_iff]`.

Establish `h2` using `(aeval_dehomCoords_of_homog (flatCone x) c hsa').symm.trans h1`. Conclude with `hsP (mem_orbitIdeal_of_aeval_eq_zero x hsa' ((mul_eq_zero.mp h2).resolve_right (prod_inv_pow_ne_zero _ c hxc _)))`. Conclude with `SubringPrimeMaximal.proof (ratioField x) (chartRing x c) _ hprime hne`.
-/
theorem proof : Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  obtain ⟨hVmin, -⟩ := hV
  have : V.IsPrime := hVmin.1.1
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, -, hsa, hsP⟩ := hs
  have hsa' : IsWeightedHomogeneous (coordDeg n) s a := (geoMultiHomog_iff s a).mp hsa

  have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
    have hJ : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by
      intro f hf b
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hf
      rw [map_add]
      exact Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b)
        (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)
    exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin

  have hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hPV ?_)
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [h0]
  have hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0 := fun k ↦ genPt_ne_zero V (hc k)

  have hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0 := by
    intro f hf
    classical
    rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    exact (aeval_dehomCoords_of_homog (genPt V) c
      (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)

  have hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F hF
    rw [chartEval_eq_zero_iff] at hF
    have hF' := (aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF
    have hH := (mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)
    have hHV : homogenize c F ∈ V :=
      hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)
    exact (aeval_dehomCoords (genPt V) c hyc F).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)

  have hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔
      aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F
    constructor
    · intro hF
      obtain ⟨v, hv, hvF⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF
      have h1 := hker (F - v) (by rw [map_sub, hvF, sub_self])
      rwa [map_sub, hVzero v hv, sub_zero] at h1
    · intro hF
      have hF' := (aeval_dehomCoords (genPt V) c hyc F).symm.trans hF
      have hH := (aeval_genPt_eq_zero_iff V _).mp
        ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))
      have e : chartEval x c (homogenize c F) = chartEval x c F :=
        map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F
      rw [← e]
      exact Ideal.mem_map_of_mem _ hH
  have hprime : (chartPoint x c V).IsPrime := by
    refine ⟨fun htop ↦ ?_, fun {u v} huv ↦ ?_⟩
    · have h1 : chartEval x c 1 ∈ chartPoint x c V := by rw [htop]; exact Submodule.mem_top
      rw [hmem, map_one] at h1
      exact one_ne_zero h1
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      obtain ⟨G, rfl⟩ := chartEval_surjective x c v
      rw [← map_mul, hmem, map_mul] at huv
      rcases mul_eq_zero.mp huv with h | h
      · exact Or.inl ((hmem F).mpr h)
      · exact Or.inr ((hmem G).mpr h)
  have hne : chartPoint x c V ≠ ⊥ := by
    intro hbot
    have h1 : chartEval x c s ∈ chartPoint x c V := Ideal.mem_map_of_mem _ hsV
    rw [hbot, Ideal.mem_bot, chartEval_eq_zero_iff] at h1
    have h2 := (aeval_dehomCoords_of_homog (flatCone x) c hsa').symm.trans h1
    exact hsP (mem_orbitIdeal_of_aeval_eq_zero x hsa'
      ((mul_eq_zero.mp h2).resolve_right (prod_inv_pow_ne_zero _ c hxc _)))
  exact SubringPrimeMaximal.proof (ratioField x) (chartRing x c) _ hprime hne

end OrbitChartMax

end

end GroundTheory.Heights₂.Heights
