import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FramedTwoCoboundaries
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem integral_normSq_coef {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} :
    ∫ g, f g * star (f g) ∂μ = ((∫ g, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem inner_self_C {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  simp

/- English proof (translation)
Take `⟨hd, hF⟩` from `h`. Establish `e` using `(hF v v v v).2`. Rewrite `e` using `[integral_normSq_coef, inner_self_C]`. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.2 hv`. Establish `e' : (∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ) = ‖v‖ ^ 4 / d`.

Establish `: (((∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ : ℝ)) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ)`. Rewrite using `[e]`. Use `push_cast`. Put the polynomial expressions in normal form. Conclude with `this` after adjusting the coercions.

Unfold `fdegOf`. Rewrite using `[e']`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegOf_eq {μ : Measure (Formalism.REAL.UJ ε)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg μ σ d) {v : H} (hv : v ≠ 0) : fdegOf μ σ v = d := by
  obtain ⟨hd, hF⟩ := h
  have e := (hF v v v v).2
  rw [integral_normSq_coef, inner_self_C] at e
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e' : (∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ) = ‖v‖ ^ 4 / d := by
    have : (((∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ : ℝ)) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [e]; push_cast; ring_nf
    exact_mod_cast this
  unfold fdegOf
  rw [e']
  field_simp

end Fdeg

section SchurH

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Take `⟨P, hP, hDS⟩` from `hσ`. Establish `: CompleteSpace H` using `hDS.1`. Take `⟨d, hd, hF⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ _ hDS`. Take `⟨c, hc0, hcT, rfl⟩` from `Formalism.MainNotions.LeviCoordinates.haar_eq_smul_cayley_image hP hμ`. Establish `hemb` using `Formalism.MainNotions.LeviCoordinates.cayleyEmbedding_measurable hP`.

Establish `hcpos : 0 < c.toReal` using `ENNReal.toReal_pos hc0 hcT`. Use `⟨d / c.toReal, div_pos hd hcpos, fun v w v' w' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `Integrable.smul_measure ?_ hcT` and prove the remaining obligations. Rewrite using `[hemb.integrable_map_iff]`. Conclude with `(hF v w v' w').1`.

Rewrite using `[integral_smul_measure, hemb.integral_map]`. Establish `h2` using `(hF v w v' w').2`. Establish `h3 : ∫ g, inner ℂ w (σ (Matrix.of (Formalism.MainNotions.LeviCoordinates.cayleyEmbedding P g)) v) * star (inner ℂ w' (σ (Matrix.of (Formalism.MainNotions.LeviCoordinates.cayleyEmbedding P g)) v')) ∂(Formalism.REAL.muG ε) = inner ℂ v' v * inner ℂ w w' / (d : ℂ)` using `h2`. Rewrite using `[h3]`. Establish `hc' : ((c.toReal : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hcpos.ne'`.

Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Rewrite using `[Complex.real_smul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem schurH {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (hσ : IsDSHpk k r ε lam σ)
    {μG : Measure (Mt k r)} (hμ : IsHaarOn (UH (Hpk k r)) μG) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have : CompleteSpace H := hDS.1
  obtain ⟨d, hd, hF⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ _ hDS
  obtain ⟨c, hc0, hcT, rfl⟩ := Formalism.MainNotions.LeviCoordinates.haar_eq_smul_cayley_image hP hμ
  have hemb := Formalism.MainNotions.LeviCoordinates.cayleyEmbedding_measurable hP
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hcT
  refine ⟨d / c.toReal, div_pos hd hcpos, fun v w v' w' => ⟨?_, ?_⟩⟩
  · refine Integrable.smul_measure ?_ hcT
    rw [hemb.integrable_map_iff]
    exact (hF v w v' w').1
  · rw [integral_smul_measure, hemb.integral_map]
    have h2 := (hF v w v' w').2
    have h3 : ∫ g, inner ℂ w (σ (Matrix.of (Formalism.MainNotions.LeviCoordinates.cayleyEmbedding P g)) v) *
        star (inner ℂ w' (σ (Matrix.of (Formalism.MainNotions.LeviCoordinates.cayleyEmbedding P g)) v')) ∂(Formalism.REAL.muG ε) =
        inner ℂ v' v * inner ℂ w w' / (d : ℂ) := h2
    rw [h3]
    have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp

/- English proof (translation)
Establish `e` using `hS w0 w0 w0 w0`. Establish `hI : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG = ((∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ)` using `integral_normSq_coef`. Rewrite `e` using `[hI, inner_self_C]`. Establish `hn : 0 < ‖w0‖` using `norm_pos_iff.2 hw`. Establish `e' : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d`.

Establish `: (((∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG : ℝ)) : ℂ) = ((‖w0‖ ^ 4 / d : ℝ) : ℂ)`. Rewrite using `[e]`. Use `push_cast`. Put the polynomial expressions in normal form. Conclude with `this` after adjusting the coercions.

Unfold `fdegH`. Rewrite using `[e']`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegH_eq {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {μG : Measure (Mt k r)} {d : ℝ}
    (hd : 0 < d) (hS : ∀ v w v' w' : H,
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w0 : H} (hw : w0 ≠ 0) : fdegH μG σ w0 = d := by
  have e := hS w0 w0 w0 w0
  have hI : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ((∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) := integral_normSq_coef
  rw [hI, inner_self_C] at e
  have hn : 0 < ‖w0‖ := norm_pos_iff.2 hw
  have e' : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have : (((∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG : ℝ)) : ℂ) = ((‖w0‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [e]; push_cast; ring_nf
    exact_mod_cast this
  unfold fdegH
  rw [e']
  field_simp

end SchurH

section P90P

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Take `⟨P, hP, hDS⟩` from `hσ`. Establish `h` using `hDS.2.2.1.1.1`. Establish `hu : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hP.1.1`. Simplify `h` using `[Matrix.nonsing_inv_mul _ hu]`.
-/
theorem ds_one (hσ : IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h := hDS.2.2.1.1.1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  simpa [Matrix.nonsing_inv_mul _ hu] using h

/- English proof (translation)
Establish `h1` using `Formalism.MainNotions.LeviCoordinates.discrete_series_inner hσ ha (σ a⁻¹ y) z`. Establish `h2 : σ a (σ a⁻¹ y) = y`. Establish `e : σ (a * a⁻¹) = (σ a).comp (σ a⁻¹)` using `Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha (uh_inv ha)`. Rewrite `e` using `[Matrix.mul_nonsing_inv _ (isUnit_of_uh ha), ds_one hσ]`. Use `congrArg (fun T : H →L[ℂ] H => T y) e` as an intermediate fact.

Simplify using `using this.symm`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.
-/
theorem ds_inv_adj (hσ : IsDSHpk k r ε lam σ) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (y z : H) : ⟪σ a⁻¹ y, z⟫_ℂ = ⟪y, σ a z⟫_ℂ := by
  have h1 := Formalism.MainNotions.LeviCoordinates.discrete_series_inner hσ ha (σ a⁻¹ y) z
  have h2 : σ a (σ a⁻¹ y) = y := by
    have e : σ (a * a⁻¹) = (σ a).comp (σ a⁻¹) := Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha (uh_inv ha)
    rw [Matrix.mul_nonsing_inv _ (isUnit_of_uh ha), ds_one hσ] at e
    have := congrArg (fun T : H →L[ℂ] H => T y) e
    simpa using this.symm
  rw [h2] at h1
  exact h1.symm

/- English proof (translation)
Use `set fb := stdOrthonormalBasis ℂ Wp`. Use `set eb := stdOrthonormalBasis ℂ Wq`. Establish `hrep : σ (a⁻¹ * x * b) = ((σ a⁻¹).comp (σ x)).comp (σ b)`. Rewrite using `[Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ (uh_mul (uh_inv ha) hx) hb, Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ (uh_inv ha) hx]`. Unfold `hsInner`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, hrep]`. Use `congr 1`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.

Use `set v := P (σ x (Q (eb i)))`. Use `set u := P (σ a⁻¹ (σ x (σ b (Q (C (eb i))))))`. Establish `hv : v = ∑ c, ⟪fb c, v⟫_ℂ • fb c` using `(fb.sum_repr' v).symm`. Use `conv_lhs => rw [hv]`. Rewrite using `[map_sum, inner_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_right]`. Use `congr 1`. Simplify using `only [v]`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.

Simplify using `only [u]`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, ds_inv_adj hσ ha, ← inner_conj_symm]`. Both sides reduce to the same expression.
-/
theorem hs_point {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (hσ : IsDSHpk k r ε lam σ) (P : H →L[ℂ] Wp) (Q : Wq →L[ℂ] H) (A : Wp →L[ℂ] Wp) (C : Wq →L[ℂ] Wq) (τ : ℂ)
    {a b x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    hsInner (P.comp ((σ x).comp Q)) (τ • ((ContinuousLinearMap.adjoint A).comp ((P.comp ((σ (a⁻¹ * x * b)).comp Q)).comp C))) =
      star τ * ∑ i, ∑ c, ⟪ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ Wp c), σ x (Q (stdOrthonormalBasis ℂ Wq i))⟫_ℂ *
        star ⟪σ a (ContinuousLinearMap.adjoint P (A (stdOrthonormalBasis ℂ Wp c))),
          σ x (σ b (Q (C (stdOrthonormalBasis ℂ Wq i))))⟫_ℂ := by
  set fb := stdOrthonormalBasis ℂ Wp
  set eb := stdOrthonormalBasis ℂ Wq
  have hrep : σ (a⁻¹ * x * b) = ((σ a⁻¹).comp (σ x)).comp (σ b) := by
    rw [Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ (uh_mul (uh_inv ha) hx) hb, Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ (uh_inv ha) hx]
  unfold hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, hrep]
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  set v := P (σ x (Q (eb i)))
  set u := P (σ a⁻¹ (σ x (σ b (Q (C (eb i))))))
  have hv : v = ∑ c, ⟪fb c, v⟫_ℂ • fb c := (fb.sum_repr' v).symm
  conv_lhs => rw [hv]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, inner_smul_right]
  congr 1
  · simp only [v]
    rw [ContinuousLinearMap.adjoint_inner_left]
  · simp only [u]
    rw [← ContinuousLinearMap.adjoint_inner_right, ds_inv_adj hσ ha, ← inner_conj_symm]
    rfl

/- English proof (translation)
Rewrite using `[integral_congr_ae (hμ.mono fun x hx => hs_point hσ P Q A C τ ha hb hx)]`. Rewrite using `[integral_const_mul]`. Use `congr 1`. Rewrite using `[integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun c _ => (hS _ _ _ _).1))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_finsetSum _ (fun c _ => (hS _ _ _ _).1)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Conclude with `(hS _ _ _ _).2`.
-/
theorem inner_int {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (hσ : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hμ : ∀ᵐ x ∂μG, Matrix.of x ∈ UH (Hpk k r)) {d : ℝ}
    (hS : ∀ v w v' w' : H,
      Integrable (fun x => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (P : H →L[ℂ] Wp) (Q : Wq →L[ℂ] H) (A : Wp →L[ℂ] Wp) (C : Wq →L[ℂ] Wq) (τ : ℂ)
    {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    ∫ x, hsInner (P.comp ((σ (Matrix.of x)).comp Q))
        (τ • ((ContinuousLinearMap.adjoint A).comp ((P.comp ((σ (a⁻¹ * Matrix.of x * b)).comp Q)).comp C))) ∂μG =
      star τ * ∑ i, ∑ c, ⟪σ b (Q (C (stdOrthonormalBasis ℂ Wq i))), Q (stdOrthonormalBasis ℂ Wq i)⟫_ℂ *
        ⟪ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ Wp c),
          σ a (ContinuousLinearMap.adjoint P (A (stdOrthonormalBasis ℂ Wp c)))⟫_ℂ / (d : ℂ) := by
  rw [integral_congr_ae (hμ.mono fun x hx => hs_point hσ P Q A C τ ha hb hx)]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun c _ => (hS _ _ _ _).1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun c _ => (hS _ _ _ _).1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hS _ _ _ _).2

def betaInf (L : LocBessel k r) (μG : Measure (Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) : ℂ :=
  ∫ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
    ∫ x, hsInner (F (Matrix.of x))
      ((psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2))) •
        ((ContinuousLinearMap.adjoint (L.π (Matrix.of p.1.1)⁻¹)).comp
          ((F ((Matrix.of p.1.1 * Matrix.of p.1.2)⁻¹ * Matrix.of x * (Matrix.of p.2.1 * Matrix.of p.2.2))).comp
            (L.π' (Matrix.of p.2.1)⁻¹)))) ∂μG
    ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN))

def lfun (L : LocBessel k r) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (P : H →L[ℂ] L.Wp)
    (p : Mt k r × Mt k r) : ℂ :=
  star (psi k r L.z L.c (Matrix.of p.2)) *
    ∑ c, ⟪ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ L.Wp c),
      σ (Matrix.of p.1 * Matrix.of p.2) (ContinuousLinearMap.adjoint P (L.π (Matrix.of p.1)⁻¹ (stdOrthonormalBasis ℂ L.Wp c)))⟫_ℂ

def rfun (L : LocBessel k r) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (Q : L.Wq →L[ℂ] H)
    (p : Mt k r × Mt k r) : ℂ :=
  psi k r L.z' L.c (Matrix.of p.2) *
    ∑ i, ⟪σ (Matrix.of p.1 * Matrix.of p.2) (Q (L.π' (Matrix.of p.1)⁻¹ (stdOrthonormalBasis ℂ L.Wq i))),
      Q (stdOrthonormalBasis ℂ L.Wq i)⟫_ℂ

/- English proof (translation)
The claim follows from `((Measure.quasiMeasurePreserving_fst).ae hp).and ((Measure.quasiMeasurePreserving_snd).ae hq)`.
-/
theorem ae_prod_both {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {p : α → Prop} {q : β → Prop} (hp : ∀ᵐ x ∂μ, p x) (hq : ∀ᵐ y ∂ν, q y) : ∀ᵐ z ∂μ.prod ν, p z.1 ∧ q z.2 :=
  ((Measure.quasiMeasurePreserving_fst).ae hp).and ((Measure.quasiMeasurePreserving_snd).ae hq)

/- English proof (translation)
The claim follows from `ae_iff.2 h.2.2.1`.
-/
theorem ae_of_haar {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ S :=
  ae_iff.2 h.2.2.1

/- English proof (translation)
Establish `: SigmaFinite μW` using `hW.1`. Establish `: SigmaFinite μN` using `hN.1`. Establish `hC : MeasurableSet {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}` using `(show IsClosed {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} from Formalism.MainNotions.LeviCoordinates.isClosed_unitary_group k r).measurableSet`. Use `set A : Set (Mt k r) := {y | Matrix.of y ∉ UH (Hpk k r)} with hAdef`. Establish `hA : MeasurableSet A` using `hC.compl`.

Establish `hmc : Continuous (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r))`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Conclude with `continuous_finsetSum _ fun l _ => by fun_prop`. Establish `hm : Measurable (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)` using `hmc.measurable`.

Establish `hSae : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ UH (Hpk k r)`. Unfold `muSof`. Rewrite using `[ae_map_iff hm.aemeasurable hC]`. Conclude with `(ae_prod_both (ae_of_haar hW) (ae_of_haar hN)).mono fun p hp => uh_mul hp.1.1 hp.2.1`. Establish `hSu : muSof μW μN Set.univ ≠ 0`.

Unfold `muSof`. Rewrite using `[Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, hW1, one_mul]`. Conclude with `Measure.measure_univ_ne_zero.2 hN.2.1`. Establish `h0 : μG A = 0` using `hG.2.2.1`. Establish `e` using `hq (A.indicator 1) (measurable_one.indicator hA)`.

Rewrite `e` using `[lintegral_indicator_one hA, h0]`. Establish `hle : ∫⁻ x, A.indicator (fun _ => muSof μW μN Set.univ) x ∂νq ≤ ∫⁻ x, (∫⁻ s, A.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ A`. Rewrite using `[Set.indicator_of_mem hx, ← lintegral_one]`.

Use `le_of_eq (lintegral_congr_ae (hSae.mono fun s hs => ?_)).symm` and prove the remaining obligations. Establish `hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ A`. Introduce `hin`. Apply `hx` to reduce the goal to its premises. Establish `hu` using `isUnit_of_uh hs`.

Establish `e1 : (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x` using `Matrix.nonsing_inv_mul_cancel_left _ _ hu`. Use `show Matrix.of x ∈ UH (Hpk k r)`. Rewrite using `[← e1]`. Conclude with `uh_mul (uh_inv hs) hin`. Rewrite using `[Set.indicator_of_mem hsx]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx]`. Conclude with `bot_le`. Rewrite `hle` using `[← e, lintegral_indicator_const hA]`. Establish `hq0 : νq A = 0`.

Break down `(mul_eq_zero.1 (le_zero_iff.1 hle)) with h | h` into its components or cases. Conclude with `absurd h hSu`. Conclude with `h`. Conclude with `ae_iff.2 hq0`.
-/
theorem quot_ae {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN νq : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) (hN : IsHaarOn (Nset k r) μN)
    (hq : IsQuotMeas μG (muSof μW μN) νq) : ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := by
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hC : MeasurableSet {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} :=
    (show IsClosed {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} from Formalism.MainNotions.LeviCoordinates.isClosed_unitary_group k r).measurableSet
  set A : Set (Mt k r) := {y | Matrix.of y ∉ UH (Hpk k r)} with hAdef
  have hA : MeasurableSet A := hC.compl
  have hmc : Continuous (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun l _ => by fun_prop
  have hm : Measurable (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := hmc.measurable
  have hSae : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ UH (Hpk k r) := by
    unfold muSof
    rw [ae_map_iff hm.aemeasurable hC]
    exact (ae_prod_both (ae_of_haar hW) (ae_of_haar hN)).mono fun p hp => uh_mul hp.1.1 hp.2.1
  have hSu : muSof μW μN Set.univ ≠ 0 := by
    unfold muSof
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, hW1, one_mul]
    exact Measure.measure_univ_ne_zero.2 hN.2.1
  have h0 : μG A = 0 := hG.2.2.1
  have e := hq (A.indicator 1) (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA, h0] at e
  have hle : ∫⁻ x, A.indicator (fun _ => muSof μW μN Set.univ) x ∂νq ≤
      ∫⁻ x, (∫⁻ s, A.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae (hSae.mono fun s hs => ?_)).symm
      have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ A := by
        intro hin
        apply hx
        have hu := isUnit_of_uh hs
        have e1 : (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x :=
          Matrix.nonsing_inv_mul_cancel_left _ _ hu
        show Matrix.of x ∈ UH (Hpk k r)
        rw [← e1]
        exact uh_mul (uh_inv hs) hin
      rw [Set.indicator_of_mem hsx]
      rfl
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  rw [← e, lintegral_indicator_const hA] at hle
  have hq0 : νq A = 0 := by
    rcases (mul_eq_zero.1 (le_zero_iff.1 hle)) with h | h
    · exact absurd h hSu
    · exact h
  exact ae_iff.2 hq0

def withDS (L : LocBessel k r) (μ : Fin (2 * r + k + 1) → ℝ) (hμ : IsHCParam μ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsDSHpk k r L.ε μ σ) : LocBessel k r where
  ε := L.ε
  lam := μ
  hlam := hμ
  z := L.z
  z' := L.z'
  hz := L.hz
  hz' := L.hz'
  u := L.u
  u' := L.u'
  Hs := H
  σ := σ
  hσ := hσ
  Wp := L.Wp
  π := L.π
  hπ := L.hπ
  Wq := L.Wq
  π' := L.π'
  hπ' := L.hπ'
  c := L.c
  μW := L.μW
  μW' := L.μW'
  hμW := L.hμW
  hμW' := L.hμW'
  κN := L.κN

def swapL (L : LocBessel k r) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := L.z'
  z' := L.z
  hz := L.hz'
  hz' := L.hz
  u := L.u'
  u' := L.u
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wq
  π := L.π'
  hπ := L.hπ'
  Wq := L.Wp
  π' := L.π
  hπ' := L.hπ
  c := L.c
  μW := L.μW'
  μW' := L.μW
  hμW := L.hμW'
  hμW' := L.hμW
  κN := L.κN

end P90P

section Named

open Formalism.QuantumDeterminants.WeylGroupFacts

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

def BeSide {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ w ∈ smoothVecs (k := k) (r := r) σ, ∃ v : H, IsKFinHpk (k := k) (r := r) σ v ∧
    ∫ p : Mt k r × Mt k r,
      (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

def BeNz (D : D7) (Ch Cg Cq Cg₀ : ℝ) : Prop :=
  1 ≤ Cq → Cg₀ ≤ Cg →
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (B : H → L.Wp) (B' : H → L.Wq),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
    IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) σ L.π B →
    IsBesselMapSm L.z' (psi D.R.k D.R.rS L.z' L.c) σ L.π' B' →
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, l2SG νq (fun g => B (σ g v)) = (‖v‖₊ : ENNReal) ^ 2) →
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, l2SG νq' (fun g => B' (σ g v)) = (‖v‖₊ : ENNReal) ^ 2) →
    BeSide L.z L.c L.π L.μW L.μN σ ∧ BeSide L.z' L.c L.π' L.μW' L.μN σ

def LemmaBInf (D : D7) (Ch Cg Cq Cg₀ : ℝ) : Prop :=
  1 ≤ Cq → Cg₀ ≤ Cg →
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (μG : Measure (Mt D.R.k D.R.rS)),
    IsSection D.R.k D.R.rS L.z L.z' μsec → IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG →
    ∃ cM : ℝ, 0 < cM ∧
      ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (P : H →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] H),
        NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ →
        (∀ x, IsKFinHpk (k := D.R.k) (r := D.R.rS) σ (ContinuousLinearMap.adjoint P x)) →
        (∀ x, IsKFinHpk (k := D.R.k) (r := D.R.rS) σ (Q x)) →
        jNorm2 L (fun g => P.comp ((σ g).comp Q)) μsec =
          ENNReal.ofReal (cM * (betaInf L μG (fun g => P.comp ((σ g).comp Q))).re)

end Named

end Formalism.MainNotions.DiscreteSeriesInnerProducts
