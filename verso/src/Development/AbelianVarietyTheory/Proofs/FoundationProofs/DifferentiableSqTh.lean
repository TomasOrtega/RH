import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

def sqTh (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ (v + z) * sgStar Λ (v - z) / sgStar Λ v ^ 2

def AlgEnt (F : ℂ → ℂ) : Prop := Differentiable ℂ F ∧ ∀ n, coef1 F n ∈ Qbar

def IntSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop := ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1

def BddSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop :=
  ∃ B : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ B

def lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) : PowerSeries K :=
  e - PowerSeries.C x * PowerSeries.X ^ 2

def IsWpSer {K : Type*} [CommRing K] (a b : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 1 ∧
    (PowerSeries.X * PowerSeries.derivativeFun P - 2 * P) ^ 2 =
      4 * P ^ 3 - PowerSeries.C a * PowerSeries.X ^ 4 * P - PowerSeries.C b * PowerSeries.X ^ 6

def xAt {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC g.lam (wpF g.abelian₂ v) - g.C.r)

variable {Λ : AddSubgroup ℂ}

/- English proof (translation)
The claim follows from `(GlobalTheory.OddTheta.sgStar_laws Λ h).1.1`.
-/
theorem IsLat.differentiable (h : IsLat Λ) : Differentiable ℂ (sgStar Λ) :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.1

/- English proof (translation)
The claim follows from `(GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.1 z`.
-/
theorem IsLat.sg_neg (h : IsLat Λ) (z : ℂ) : sgStar Λ (-z) = -sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.1 z

/- English proof (translation)
The claim follows from `(GlobalTheory.OddTheta.sgStar_laws Λ h).2.1 z`.
-/
theorem IsLat.sg_eq_zero (h : IsLat Λ) (z : ℂ) : sgStar Λ z = 0 ↔ z ∈ Λ :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).2.1 z

/- English proof (translation)
The claim follows from `(GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω z`.
-/
theorem IsLat.sg_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω z

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ h`. Establish `: (Λ : Set ℂ) = (L.lattice : Set ℂ)` using `Set.ext fun z => hL z`. Rewrite using `[this]`. Conclude with `GlobalTheory.dense_compl_lattice L`.
-/
theorem IsLat.dense_compl (h : IsLat Λ) : Dense (Λ : Set ℂ)ᶜ := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun z => hL z
  rw [this]
  exact GlobalTheory.dense_compl_lattice L

/- English proof (translation)
Use `h.differentiable` as an intermediate fact. Unfold `sqTh`. Use `fun_prop`.
-/
theorem IsLat.differentiable_sqTh (h : IsLat Λ) (v : ℂ) : Differentiable ℂ (sqTh Λ v) := by
  have := h.differentiable
  unfold sqTh
  fun_prop

/- English proof (translation)
Simplify using `only [sqTh, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]`.
-/
theorem sqTh_neg (v z : ℂ) : sqTh Λ v (-z) = sqTh Λ v z := by
  simp only [sqTh, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/- English proof (translation)
Use `(h.sg_eq_zero v).not.2 hv` as an intermediate fact. Simplify using `only [sqTh, add_zero, sub_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem IsLat.sqTh_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) : sqTh Λ v 0 = 1 := by
  have := (h.sg_eq_zero v).not.2 hv
  simp only [sqTh, add_zero, sub_zero]
  field_simp

/- English proof (translation)
Use `(h.sg_eq_zero v).not.2 hv` as an intermediate fact. Simplify using `[sqTh, this, h.sg_eq_zero]`.
-/
theorem IsLat.sqTh_eq_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    sqTh Λ v z = 0 ↔ v + z ∈ Λ ∨ v - z ∈ Λ := by
  have := (h.sg_eq_zero v).not.2 hv
  simp [sqTh, this, h.sg_eq_zero]

/- English proof (translation)
Establish `h0` using `(h.sg_eq_zero v).not.2 hv`. Establish `h1` using `(GlobalTheory.OddTheta.sgStar_laws Λ h).2.2.2.1 v z hv hz`. Rewrite using `[sqTh, div_eq_iff (pow_ne_zero 2 h0)]`. Take the linear combination `h1`.
-/
theorem IsLat.sqTh_eq (h : IsLat Λ) {v z : ℂ} (hv : v ∉ Λ) (hz : z ∉ Λ) :
    sqTh Λ v z = sgStar Λ z ^ 2 * (wpF Λ z - wpF Λ v) := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).2.2.2.1 v z hv hz
  rw [sqTh, div_eq_iff (pow_ne_zero 2 h0)]
  linear_combination h1

/- English proof (translation)
Establish `h1` using `(h.differentiable_sqTh v).continuous`. Establish `h2` using `(h.differentiable_sqTh w).continuous`. Establish `h3` using `h.differentiable.continuous`. Use `congrFun (Continuous.ext_on h.dense_compl h1 (g := fun z => sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2) (by fun_prop) fun z hz => ?_) z` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[h.sqTh_eq hv hz, h.sqTh_eq hw hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsLat.sqTh_sub (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) (z : ℂ) :
    sqTh Λ v z = sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2 := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h2 := (h.differentiable_sqTh w).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl h1
    (g := fun z => sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  rw [h.sqTh_eq hv hz, h.sqTh_eq hw hz]
  ring

/- English proof (translation)
Rewrite using `[← h.sqTh_eq_zero hv, h.sqTh_eq hv hw]`. Simplify using `[(h.sg_eq_zero w).not.2 hw, sub_eq_zero]`.
-/
theorem IsLat.wp_eq_iff (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) :
    wpF Λ w = wpF Λ v ↔ v + w ∈ Λ ∨ v - w ∈ Λ := by
  rw [← h.sqTh_eq_zero hv, h.sqTh_eq hv hw]
  simp [(h.sg_eq_zero w).not.2 hw, sub_eq_zero]

/- English proof (translation)
Establish `h0` using `(h.sg_eq_zero v).not.2 hv`. Establish `e : ∀ z : ℂ, U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z = -(sgStar Λ (v + z) * sgStar Λ (v - z)) * Complex.exp (-((Real.pi : ℂ) * v * (starRingEnd ℂ) v / (area Λ : ℂ)))`. Introduce `z`. Simplify using `only [U1]`. Rewrite using `[show z + -v = -(v - z) by ring, h.sg_neg, add_comm z v, mul_mul_mul_comm, ← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `congr 1`. Simplify using `only [map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, e, sqTh]`. Simplify using `only [add_zero, sub_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem IsLat.sqTh_mul (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    (U1 Λ v (sgStar Λ) 0 * U1 Λ (-v) (sgStar Λ) 0) * sqTh Λ v z =
      U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have e : ∀ z : ℂ, U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z =
      -(sgStar Λ (v + z) * sgStar Λ (v - z)) *
        Complex.exp (-((Real.pi : ℂ) * v * (starRingEnd ℂ) v / (area Λ : ℂ))) := by
    intro z
    simp only [U1]
    rw [show z + -v = -(v - z) by ring, h.sg_neg, add_comm z v, mul_mul_mul_comm, ← Complex.exp_add]
    congr 1
    · ring
    · congr 1
      simp only [map_neg]
      ring
  rw [e, e, sqTh]
  simp only [add_zero, sub_zero]
  field_simp

end GlobalTheory.EvenTheta
