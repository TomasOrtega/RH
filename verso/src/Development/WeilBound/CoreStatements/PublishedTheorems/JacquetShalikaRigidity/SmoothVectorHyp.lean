import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SmoothVectorHyp

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

structure Hyp (E : Type) [Field E] [NumberField E] (k : ℕ) : Prop where
  cont : Continuous (dmin : GA E k → ℝ)
  pos : ∀ g : GA E k, 0 < dmin g
  rt : ∀ h : GA E k, ∃ B : ℝ, 1 ≤ B ∧ ∀ g, dmin (g * h) ≤ B * dmin g

/- English proof (translation)
Break down `le_total 1 b with h1 | h1` into its components or cases. Rewrite using `[min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)`. Rewrite using `[min_eq_right h1]`. Conclude with `(min_le_right _ _).trans h`.
-/
lemma min_le_of (a b D : ℝ) (hD : 1 ≤ D) (h : a ≤ D * b) : min 1 a ≤ D * min 1 b := by
  rcases le_total 1 b with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h1]; exact (min_le_right _ _).trans h

/- English proof (translation)
The claim follows from `pow_pos (lt_min one_pos (H.pos g)) M`.
-/
lemma wt_pos (H : Hyp E k) (M : ℕ) (g : GA E k) : 0 < wt M g :=
  pow_pos (lt_min one_pos (H.pos g)) M

/- English proof (translation)
The claim follows from `pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)`.
-/
lemma wt_le_one (H : Hyp E k) (M : ℕ) (g : GA E k) : wt M g ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)

/- English proof (translation)
The claim follows from `(continuous_const.min H.cont).pow M`.
-/
lemma wt_cont (H : Hyp E k) (M : ℕ) : Continuous (wt M : GA E k → ℝ) :=
  (continuous_const.min H.cont).pow M

/- English proof (translation)
Unfold `wt`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M`.
-/
lemma wt_le (H : Hyp E k) (M : ℕ) (g c : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (h : dmin (g * c) ≤ D * dmin g) : wt M (g * c) ≤ D ^ M * wt M g := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M

def W (H : Hyp E k) (M : ℕ) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M g : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (wt_cont H M)) 1 fun g => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos H M g).le]
      exact wt_le_one H M g

/- English proof (translation)
The claim follows from `Complex.continuous_ofReal.comp (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')`.
-/
lemma ratio_cont (H : Hyp E k) (M : ℕ) (h : GA E k) :
    Continuous fun g : GA E k => ((wt M (g * h) / wt M g : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')

/- English proof (translation)
Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]`. Conclude with `wt_le H M g h D hD hd`.
-/
lemma ratio_le (H : Hyp E k) (M : ℕ) (h g : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : dmin (g * h) ≤ D * dmin g) : ‖((wt M (g * h) / wt M g : ℝ) : ℂ)‖ ≤ D ^ M := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]
  exact wt_le H M g h D hD hd

def Q (H : Hyp E k) (M : ℕ) (h : GA E k) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M (g * h) / wt M g : ℝ) : ℂ))
    (ratio_cont H M h) ((H.rt h).choose ^ M) fun g =>
      ratio_le H M h g _ (H.rt h).choose_spec.1 ((H.rt h).choose_spec.2 g)

/- English proof (translation)
The claim follows from `(BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g => ratio_le H M h g D hD (hd g)`.
-/
lemma norm_Q_le (H : Hyp E k) (M : ℕ) (h : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ g, dmin (g * h) ≤ D * dmin g) : ‖Q H M h‖ ≤ D ^ M :=
  (BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g =>
    ratio_le H M h g D hD (hd g)

def rho (H : Hyp E k) (M : ℕ) : GA E k →* (XB E k →L[ℂ] XB E k) where
  toFun h := (ContinuousLinearMap.mul ℂ (XB E k) (Q H M h)).comp (Rt E k h)
  map_one' := by
    ext x g
    change ((wt M (g * 1) / wt M g : ℝ) : ℂ) * x (g * 1) = x g
    rw [mul_one, div_self (wt_pos H M g).ne', Complex.ofReal_one, one_mul]
  map_mul' h h' := by
    ext x g
    change ((wt M (g * (h * h')) / wt M g : ℝ) : ℂ) * x (g * (h * h')) =
      ((wt M (g * h) / wt M g : ℝ) : ℂ) * (((wt M (g * h * h') / wt M (g * h) : ℝ) : ℂ) * x (g * h * h'))
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have := (wt_pos H M (g * h)).ne'
    field_simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rho_apply (H : Hyp E k) (M : ℕ) (h g : GA E k) (x : XB E k) :
    rho H M h x g = ((wt M (g * h) / wt M g : ℝ) : ℂ) * x (g * h) := rfl

def J (H : Hyp E k) (M : ℕ) : XB E k →L[ℂ] XB E k := ContinuousLinearMap.mul ℂ (XB E k) (W H M)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma J_apply (H : Hyp E k) (M : ℕ) (x : XB E k) (g : GA E k) : J H M x g = (wt M g : ℂ) * x g := rfl

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]`. Use `congr 2`. Use `(wt_pos H M g).ne'` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
lemma inter (H : Hyp E k) (M : ℕ) (h : GA E k) (x : XB E k) : J H M (rho H M h x) = Rt E k h (J H M x) := by
  ext g
  rw [J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (wt_pos H M g).ne'
  field_simp

/- English proof (translation)
Introduce `x y hxy`. Use extensionality with `g`. Establish `e` using `congrArg (fun z : XB E k => z g) hxy`. Simplify using `only [J_apply] at e`. Conclude with `mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e`.
-/
lemma inj (H : Hyp E k) (M : ℕ) : Function.Injective (J H M) := by
  intro x y hxy
  ext g
  have e := congrArg (fun z : XB E k => z g) hxy
  simp only [J_apply] at e
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A)`. Use function extensionality and compare the values at `A`. Unfold `orb`. Use `split_ifs with hA`. Conclude with `(inter H M _ x).symm`.

Conclude with `(map_zero (J H M)).symm`. Unfold `SmV`. Rewrite using `[e]`. Conclude with `hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)`.
-/
lemma smv (H : Hyp E k) (M : ℕ) (x : XB E k) (hx : SmV ((rho H M).comp (infGL E k)) x) :
    SmV (repI E k) (J H M x) := by
  have e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A) := by
    funext A
    unfold orb
    split_ifs with hA
    · exact (inter H M _ x).symm
    · exact (map_zero (J H M)).symm
  unfold SmV
  rw [e]
  exact hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)

end SmoothVectorHyp

/- English proof (translation)
Introduce `hH hK E _ _ _ k hk M`. Take `⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩` from `hH E k`. Take `⟨kc, kpos, kle, -, kcpt, -⟩` from `hK E k hk`. Establish `H : SmoothVectorHyp.Hyp E k` using `⟨kc, kpos, fun h => by`. Take `⟨B, hB, hB'⟩` from `kcpt {h} isCompact_singleton`.

Conclude with `⟨B, hB, hB' h rfl⟩⟩`. Use `⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩, fun x hx => SmoothVectorHyp.smv H M x hx⟩` and prove the remaining obligations. Establish `hne : Nonempty {ξ : Fin k → E // ξ ≠ 0}` using `⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩`. Use `⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩` and prove the remaining obligations. Take `⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖` from `⟨_, rfl⟩`.

Rewrite using `[← hP]`. Establish `hP1 : 1 ≤ P`. Rewrite using `[hP]`. Combine the linear relations using `[norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k), norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]`. Establish `hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ + ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P`.

Rewrite using `[inv_inv, hP]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : 1 ≤ max B 1 * P ^ N` using `one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)`. Establish `hDpos : 0 < max B 1 * P ^ N` using `zero_lt_one.trans_le hD`. Establish `hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g`.

Introduce `g`. Rewrite using `[← div_le_iff₀' hDpos]`. Use `show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1`. Use `le_ciInf fun ξ => ?_` and prove the remaining obligations. Rewrite using `[div_le_iff₀' hDpos]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]`. Use `_ ≤ max B 1 * P ^ N * ht g ξ.1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _)) (h1 g ξ.1 ξ.2).le`. Express the relevant statement in the definitionally equal form `‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem secondCohomologyBound_of_boundaryBound : H0 → K1 → K2 := by
  intro hH hK E _ _ _ k hk M
  obtain ⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩ := hH E k
  obtain ⟨kc, kpos, kle, -, kcpt, -⟩ := hK E k hk
  have H : SmoothVectorHyp.Hyp E k := ⟨kc, kpos, fun h => by
    obtain ⟨B, hB, hB'⟩ := kcpt {h} isCompact_singleton
    exact ⟨B, hB, hB' h rfl⟩⟩
  refine ⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩,
    fun x hx => SmoothVectorHyp.smv H M x hx⟩
  have hne : Nonempty {ξ : Fin k → E // ξ ≠ 0} :=
    ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
  refine ⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := by
    rw [hP]
    linarith [norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k),
      norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]
  have hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P := by
    rw [inv_inv, hP]; ring
  have hD : 1 ≤ max B 1 * P ^ N := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)
  have hDpos : 0 < max B 1 * P ^ N := zero_lt_one.trans_le hD
  have hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g := by
    intro g
    rw [← div_le_iff₀' hDpos]
    show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1
    refine le_ciInf fun ξ => ?_
    rw [div_le_iff₀' hDpos]
    calc dmin (g * infGL E k y) ≤ ht (g * infGL E k y) ξ.1 := kle _ _ ξ.2
      _ ≤ B * (1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
          ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
            ht (g * infGL E k y * infGL E k y⁻¹) ξ.1 := h6 y⁻¹ _ ξ.1 ξ.2
      _ = B * P ^ N * ht g ξ.1 := by
          rw [hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ ≤ max B 1 * P ^ N * ht g ξ.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _))
            (h1 g ξ.1 ξ.2).le
  change ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _
  calc ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖
        ≤ ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖Rt E k (infGL E k y) x‖ := norm_mul_le _ _
    _ = ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖x‖ := by rw [norm_Rt]
    _ ≤ (max B 1 * P ^ N) ^ M * ‖x‖ :=
        mul_le_mul_of_nonneg_right (SmoothVectorHyp.norm_Q_le H M _ _ hD hd) (norm_nonneg _)
    _ = max B 1 ^ M * P ^ (N * M) * ‖x‖ := by rw [mul_pow, ← pow_mul]

end PositivityTheory.AdelicQuotientData

end
