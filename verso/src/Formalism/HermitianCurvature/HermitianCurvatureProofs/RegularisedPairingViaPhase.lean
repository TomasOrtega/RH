import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section basics

variable {k r : ℕ}

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
theorem haar_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

/- English proof (translation)
Rewrite using `[ae_iff]`. Conclude with `h.conc`.
-/
theorem haar_ae {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, (Matrix.of g : Mat k r) ∈ U := by
  rw [ae_iff]
  exact h.conc

/- English proof (translation)
Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Unfold `aDil`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `split_ifs`. Use `push_cast`. Rewrite using `[inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]`. Simplify using the standard rewrite rules.

Use `push_cast`. Rewrite using `[inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]`.
-/
theorem aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]
  · simp
  · push_cast
    rw [inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]

/- English proof (translation)
Use `show (a * b)ᴴ * H * (a * b) = H`. Establish `ha' : aᴴ * H * a = H` using `ha`. Establish `hb' : bᴴ * H * b = H` using `hb`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_mem_uh {ι : Type*} [Fintype ι] [DecidableEq ι] {H a b : Matrix ι ι ℂ}
    (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  show (a * b)ᴴ * H * (a * b) = H
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

/- English proof (translation)
Distinguish the cases in `hA : i.val < r ∧ i.val + j.val = 2 * r + k`. Establish `e1 : ¬ j.val < r` using `by omega`. Establish `e2 : ¬ j.val ≤ r + k` using `by omega`. Establish `e3 : j.val - (r + k) = r - i.val` using `by omega`. Rewrite using `[if_pos hA.1, if_neg e1, if_neg e2, e3]`.

Rewrite using `[show star ((t ^ (r - i.val) : ℝ) : ℂ) = ((t ^ (r - i.val) : ℝ) : ℂ) from Complex.conj_ofReal _]`. Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]`. Distinguish the cases in `hB : j.val < r ∧ i.val + j.val = 2 * r + k`. Establish `e1 : ¬ i.val < r` using `by omega`. Establish `e2 : ¬ i.val ≤ r + k` using `by omega`.

Establish `e3 : i.val - (r + k) = r - j.val` using `by omega`. Rewrite using `[if_neg e1, if_neg e2, if_pos hB.1, e3]`. Rewrite using `[show star (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) = (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) from Complex.conj_ofReal _]`. Rewrite using `[← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]`. Distinguish the cases in `hC : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j`.

Take `⟨hC1, hC2, rfl⟩` from `hC`. Rewrite using `[if_neg (not_lt.2 hC1), if_pos hC2]`. Simplify using the standard rewrite rules. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises.

Unfold `Hpk`. Rewrite using `[if_neg hA, if_neg hB, if_neg hC]`.
-/
private theorem star_aDil_entry_mul_aDil_entry_eq_one {k r : ℕ} (t : ℝ) (ht : t ≠ 0) (i j : Fin (2 * r + k + 1))
    (h : Hpk k r i j ≠ 0) :
    star (if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ) else if i.val ≤ r + k then 1
      else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)) *
    (if j.val < r then ((t ^ (r - j.val) : ℝ) : ℂ) else if j.val ≤ r + k then 1
      else (((t ^ (j.val - (r + k)))⁻¹ : ℝ) : ℂ)) = 1 := by
  by_cases hA : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e1 : ¬ j.val < r := by omega
    have e2 : ¬ j.val ≤ r + k := by omega
    have e3 : j.val - (r + k) = r - i.val := by omega
    rw [if_pos hA.1, if_neg e1, if_neg e2, e3]
    rw [show star ((t ^ (r - i.val) : ℝ) : ℂ) = ((t ^ (r - i.val) : ℝ) : ℂ) from Complex.conj_ofReal _]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
  by_cases hB : j.val < r ∧ i.val + j.val = 2 * r + k
  · have e1 : ¬ i.val < r := by omega
    have e2 : ¬ i.val ≤ r + k := by omega
    have e3 : i.val - (r + k) = r - j.val := by omega
    rw [if_neg e1, if_neg e2, if_pos hB.1, e3]
    rw [show star (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) = (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
  by_cases hC : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · obtain ⟨hC1, hC2, rfl⟩ := hC
    rw [if_neg (not_lt.2 hC1), if_pos hC2]
    simp
  · exfalso
    apply h
    unfold Hpk
    rw [if_neg hA, if_neg hB, if_neg hC]

/- English proof (translation)
Use `show (aDil k r t)ᴴ * Hpk k r * aDil k r t = Hpk k r`. Unfold `aDil`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Simplify using `only [Pi.star_apply]`. Distinguish the cases in `hH : Hpk k r i j = 0`. Rewrite using `[hH]`. Simplify using the standard rewrite rules. Establish `h1` using `star_aDil_entry_mul_aDil_entry_eq_one t ht i j hH`.

Take the linear combination `(Hpk k r i j) * h1`.
-/
private theorem aDil_mem_gv {k r : ℕ} (t : ℝ) (ht : t ≠ 0) : aDil k r t ∈ GV k r := by
  show (aDil k r t)ᴴ * Hpk k r * aDil k r t = Hpk k r
  unfold aDil
  rw [Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply]
  by_cases hH : Hpk k r i j = 0
  · rw [hH]
    simp
  · have h1 := star_aDil_entry_mul_aDil_entry_eq_one t ht i j hH
    linear_combination (Hpk k r i j) * h1

/- English proof (translation)
Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Unfold `aDil`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `split_ifs`. Use `push_cast`. Rewrite using `[inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]`. Simplify using the standard rewrite rules. Use `push_cast`.

Rewrite using `[inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]`.
-/
private theorem aDil_inv_mul_aDil {k r : ℕ} (t : ℝ) (ht : t ≠ 0) : aDil k r t⁻¹ * aDil k r t = 1 := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]
  · simp
  · push_cast
    rw [inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]

/- English proof (translation)
Use `set d : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ) else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd_def`. Use `set d' : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t⁻¹ ^ (r - i.val) : ℝ) : ℂ) else if i.val ≤ r + k then 1 else (((t⁻¹ ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd'_def`. Establish `hA : aDil k r t = Matrix.diagonal d` using `rfl`. Establish `hA' : aDil k r t⁻¹ = Matrix.diagonal d'` using `rfl`. Establish `m1 : Matrix.diagonal d ∈ UH (Hpk k r)` using `aDil_mem_gv t ht`.

Establish `m2 : Matrix.diagonal d' ∈ UH (Hpk k r)` using `aDil_mem_gv t⁻¹ (inv_ne_zero ht)`. Establish `hdd : ∀ i, d i * d' i = 1`. Introduce `i`. Establish `h1` using `congrArg (fun M : Mat k r => M i i) (aDil_inv_mul_aDil (k := k) (r := r) t ht)`. Simplify using `only [hA, hA', Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1`.

Rewrite using `[mul_comm]`. Conclude with `h1`. Rewrite using `[aDil_inv k r t ht, hA, hA']`. Unfold `QuantumDeterminants.Nset at hn ⊢`. Take `⟨hU, hcol, hmid⟩` from `hn`.

Rewrite using `[Set.mem_setOf_eq]`. Use `⟨mul_mem_uh (mul_mem_uh m1 hU) m2, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, hcol a i hai]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[mul_one]`. Conclude with `hdd _`. Simplify using the standard rewrite rules. Introduce `i j hj1 hj2 hi`.

Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, hmid i j hj1 hj2 hi]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one]`. Conclude with `hdd _`.

Simplify using the standard rewrite rules.
-/
theorem dil_mem_N (t : ℝ) (ht : t ≠ 0) {n : Mat k r} (hn : n ∈ Nset k r) :
    aDil k r t * n * (aDil k r t)⁻¹ ∈ Nset k r := by
  set d : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd_def
  set d' : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t⁻¹ ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t⁻¹ ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd'_def
  have hA : aDil k r t = Matrix.diagonal d := rfl
  have hA' : aDil k r t⁻¹ = Matrix.diagonal d' := rfl
  have m1 : Matrix.diagonal d ∈ UH (Hpk k r) := aDil_mem_gv t ht
  have m2 : Matrix.diagonal d' ∈ UH (Hpk k r) := aDil_mem_gv t⁻¹ (inv_ne_zero ht)
  have hdd : ∀ i, d i * d' i = 1 := by
    intro i
    have h1 := congrArg (fun M : Mat k r => M i i) (aDil_inv_mul_aDil (k := k) (r := r) t ht)
    simp only [hA, hA', Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h1
    rw [mul_comm]
    exact h1
  rw [aDil_inv k r t ht, hA, hA']
  unfold QuantumDeterminants.Nset at hn ⊢
  obtain ⟨hU, hcol, hmid⟩ := hn
  rw [Set.mem_setOf_eq]
  refine ⟨mul_mem_uh (mul_mem_uh m1 hU) m2, ?_, ?_⟩
  · intro a i hai
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hcol a i hai]
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hdd _
    · simp
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hmid i j hj1 hj2 hi]
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hdd _
    · simp

end basics

section setting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

/- English proof (translation)
Use `haveI := haar_sigmaFinite D.haarW`. Use `haveI := haar_sigmaFinite D.haarN`. Use `haveI := haar_sigmaFinite D.haarW'`. Establish `h1` using `haar_ae D.haarW`. Establish `h2` using `haar_ae D.haarN`.

Establish `h3` using `haar_ae D.haarW'`. Establish `a1 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)`. Establish `a2 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae h3).and (Measure.quasiMeasurePreserving_snd.ae h2)`. Establish `a3` using `(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a1`. Establish `a4` using `(Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a2`.

Establish `a5` using `a3.and a4`. Unfold `RealPlaceData.μSS`. Use `filter_upwards [a5] with p hp`. Unfold `RealPlaceData.inSS`. Conclude with `⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩`.
-/
theorem ae_inSS (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  haveI := haar_sigmaFinite D.haarW
  haveI := haar_sigmaFinite D.haarN
  haveI := haar_sigmaFinite D.haarW'
  have h1 := haar_ae D.haarW
  have h2 := haar_ae D.haarN
  have h3 := haar_ae D.haarW'
  have a1 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW.prod D.μN),
      Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have a2 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW'.prod D.μN),
      Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae h3).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have a3 := (Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a1
  have a4 := (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a2
  have a5 := a3.and a4
  unfold RealPlaceData.μSS
  filter_upwards [a5] with p hp
  unfold RealPlaceData.inSS
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp ⊢`. Conclude with `⟨hp.1, dil_mem_N t₁ h1 hp.2.1, hp.2.2.1, dil_mem_N t₂ h2 hp.2.2.2⟩`.
-/
theorem dil_inSS (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {t₁ t₂ : ℝ} (h1 : t₁ ≠ 0) (h2 : t₂ ≠ 0) :
    D.inSS (dilation₂ (t₁, t₂) p) := by
  unfold RealPlaceData.inSS at hp ⊢
  exact ⟨hp.1, dil_mem_N t₁ h1 hp.2.1, hp.2.2.1, dil_mem_N t₂ h2 hp.2.2.2⟩

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h0` using `D.χ_supp (subset_tsupport _ (Function.mem_support.2 h))`. Evaluate the numerical expressions using `at h0`.
-/
theorem chi_ne (D : RealPlaceData k r Wp Wq) {t : ℝ} (h : D.χ t ≠ 0) : t ≠ 0 := by
  rintro rfl
  have h0 := D.χ_supp (subset_tsupport _ (Function.mem_support.2 h))
  norm_num at h0

end setting

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D τ F₁ F₁' F₂ F₂' h`. Unfold `betaInfTau`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [ae_inSS D] with p hp`. Establish `hreg : regBracket D F₁ F₁' p = regBracket D F₂ F₂' p`.

Use function extensionality and compare the values at `t₁ t₂`. Unfold `regBracket`. Distinguish the cases in `h0 : D.χ t₁ * D.χ t₂ = 0`. Simplify using `[h0]`. Establish `h1 : D.χ t₁ ≠ 0` using `left_ne_zero_of_mul h0`.

Establish `h2 : D.χ t₂ ≠ 0` using `right_ne_zero_of_mul h0`. Rewrite using `[h _ (dil_inSS D hp (chi_ne D h1) (chi_ne D h2))]`. Simplify using `only [hreg]`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.regularised_pairing_via_phase : Formalism.FourierDecayAlt.B.StepRegPh := by
  intro k r Wp Wq _ _ _ _ _ _ D τ F₁ F₁' F₂ F₂' h
  unfold betaInfTau
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  have hreg : regBracket D F₁ F₁' p = regBracket D F₂ F₂' p := by
    funext t₁ t₂
    unfold regBracket
    by_cases h0 : D.χ t₁ * D.χ t₂ = 0
    · simp [h0]
    · have h1 : D.χ t₁ ≠ 0 := left_ne_zero_of_mul h0
      have h2 : D.χ t₂ ≠ 0 := right_ne_zero_of_mul h0
      rw [h _ (dil_inSS D hp (chi_ne D h1) (chi_ne D h2))]
  simp only [hreg]

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (Module.finrank ℂ Wq) => Wp)).symm :
      (Fin (Module.finrank ℂ Wq) → Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)).comp
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsL_apply (A : Wq →L[ℂ] Wp) : hsL A = hsVec A := rfl

def hsK (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : ℝ :=
  ‖(hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))‖ ^ 2

/- English proof (translation)
Unfold `hsK`. Check the signs of the components of the expression.
-/
theorem hsK_nonneg : 0 ≤ hsK Wp Wq := by
  unfold hsK
  positivity

/- English proof (translation)
Use `set L := (hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) with hL`. Establish `hA : ‖hsVec A‖ ≤ ‖L‖ * ‖A‖`. Rewrite using `[← hsL_apply]`. Conclude with `L.le_opNorm A`. Establish `hB : ‖hsVec B‖ ≤ ‖L‖ * ‖B‖`.

Rewrite using `[← hsL_apply]`. Conclude with `L.le_opNorm B`. Unfold `hsInner hsK`. Rewrite using `[← hL]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hs_norm_le (A B : Wq →L[ℂ] Wp) : ‖hsInner A B‖ ≤ hsK Wp Wq * (‖A‖ * ‖B‖) := by
  set L := (hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) with hL
  have hA : ‖hsVec A‖ ≤ ‖L‖ * ‖A‖ := by
    rw [← hsL_apply]
    exact L.le_opNorm A
  have hB : ‖hsVec B‖ ≤ ‖L‖ * ‖B‖ := by
    rw [← hsL_apply]
    exact L.le_opNorm B
  unfold hsInner hsK
  rw [← hL]
  calc ‖inner ℂ (hsVec B) (hsVec A)‖ ≤ ‖hsVec B‖ * ‖hsVec A‖ := norm_inner_le_norm _ _
    _ ≤ (‖L‖ * ‖B‖) * (‖L‖ * ‖A‖) := mul_le_mul hB hA (norm_nonneg _) (by positivity)
    _ = ‖L‖ ^ 2 * (‖A‖ * ‖B‖) := by ring

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply, map_add, inner_add_right]`.
-/
theorem hs_add_left (A A' B : Wq →L[ℂ] Wp) : hsInner (A + A') B = hsInner A B + hsInner A' B := by
  simp only [hsInner, ← hsL_apply, map_add, inner_add_right]

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply, map_add, inner_add_left]`.
-/
theorem hs_add_right (A B B' : Wq →L[ℂ] Wp) : hsInner A (B + B') = hsInner A B + hsInner A B' := by
  simp only [hsInner, ← hsL_apply, map_add, inner_add_left]

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply, map_smul, inner_smul_left]`.
-/
theorem hs_smul_right (a : ℂ) (A B : Wq →L[ℂ] Wp) : hsInner A (a • B) = conj a * hsInner A B := by
  simp only [hsInner, ← hsL_apply, map_smul, inner_smul_left]

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply, map_zero, inner_zero_left]`.
-/
theorem hs_zero_right (A : Wq →L[ℂ] Wp) : hsInner A 0 = 0 := by
  simp only [hsInner, ← hsL_apply, map_zero, inner_zero_left]

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply, map_zero, inner_zero_right]`.
-/
theorem hs_zero_left (A : Wq →L[ℂ] Wp) : hsInner 0 A = 0 := by
  simp only [hsInner, ← hsL_apply, map_zero, inner_zero_right]

/- English proof (translation)
Simplify using `only [hsInner, ← hsL_apply]`. Conclude with `((hsL (Wp := Wp) (Wq := Wq)).continuous.comp continuous_snd).inner ((hsL (Wp := Wp) (Wq := Wq)).continuous.comp continuous_fst)`.
-/
theorem hs_continuous : Continuous fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => hsInner q.1 q.2 := by
  simp only [hsInner, ← hsL_apply]
  exact ((hsL (Wp := Wp) (Wq := Wq)).continuous.comp continuous_snd).inner
    ((hsL (Wp := Wp) (Wq := Wq)).continuous.comp continuous_fst)

end hs

section ck

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Use `show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
theorem GV_closed : IsClosed (GV k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg₀U, hf', he⟩` from `h g₀ hg₀`. Establish `hc : ContinuousAt f' g₀` using `hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)`. Use `hc.continuousWithinAt.congr_of_eventuallyEq ?_ (he g₀ hg₀U hg₀)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hg₀U)] with g hg hgU`.

Conclude with `he g hgU hg`.
-/
theorem ckOn_continuousOn {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) : ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', he⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (he g₀ hg₀U hg₀)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hg₀U)] with g hg hgU
  exact he g hgU hg

/- English proof (translation)
Establish `hc : IsClosed (X` using `Mt k r) (GV k r) := GV_closed`. Establish `hs : MeasurableSet (α` using `Mt k r) (GV k r) := hc.measurableSet`. Establish `hf' : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) (GV k r)` using `hf`. Establish `h1` using `hf'.aestronglyMeasurable (μ := μ) hs`. Rewrite `h1` using `[Measure.restrict_eq_self_of_ae_mem (haar_ae h)]`. Then use the resulting hypothesis.
-/
theorem aesm_of_continuousOn {μ : Measure (Mt k r)} (h : IsHaarOn (GV k r) μ) {f : Mat k r → E}
    (hf : ContinuousOn f (GV k r)) : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) μ := by
  have hc : IsClosed (X := Mt k r) (GV k r) := GV_closed
  have hs : MeasurableSet (α := Mt k r) (GV k r) := hc.measurableSet
  have hf' : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) (GV k r) := hf
  have h1 := hf'.aestronglyMeasurable (μ := μ) hs
  rwa [Measure.restrict_eq_self_of_ae_mem (haar_ae h)] at h1

end ck

section phbound

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

/- English proof (translation)
Rewrite using `[sgs, Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  rw [sgs, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Conclude with `mul_mem_uh hp.2.1.1 hp.1.1`.
-/
theorem inSS_left (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  exact mul_mem_uh hp.2.1.1 hp.1.1

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Conclude with `mul_mem_uh hp.2.2.2.1 hp.2.2.1.1`.
-/
theorem inSS_right (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  exact mul_mem_uh hp.2.2.2.1 hp.2.2.1.1

/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Establish `h1` using `hp.1`. Establish `h3` using `Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1`. Unfold `rho`. Apply `ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[ContinuousLinearMap.comp_apply, D.π_unitary _ h1, ContinuousLinearMap.comp_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rho_norm_le (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : ‖rho D p F g‖ ≤ ‖F (sgs p g)‖ := by
  unfold RealPlaceData.inSS at hp
  have h1 := hp.1
  have h3 := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1
  unfold rho
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [ContinuousLinearMap.comp_apply, D.π_unitary _ h1, ContinuousLinearMap.comp_apply]
  calc ‖F (sgs p g) (D.π' (Matrix.of p.2.1)⁻¹ v)‖ ≤ ‖F (sgs p g)‖ * ‖D.π' (Matrix.of p.2.1)⁻¹ v‖ :=
        (F (sgs p g)).le_opNorm _
    _ = ‖F (sgs p g)‖ * ‖v‖ := by rw [D.π'_unitary _ h3]

end phbound

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D Ξ A hCB`. Take `⟨C, hC⟩` from `hCB`. Use `⟨hsK Wp Wq * max C 0, fun F F' c c' hF hF' p hp => ?_⟩` and prove the remaining obligations. Establish `hK : 0 ≤ hsK Wp Wq` using `hsK_nonneg`. Establish `hb : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c` using `fun g hg => by`.

Establish `h0` using `hF.2 [] [] (by simp) (by simp) (by simp) g hg`. Use `first`. Consider the case `exact h0`. Consider the case `simpa [dLR] using h0`. Consider the case `simpa [dLR, Rw] using h0`.

Establish `hb' : ∀ g ∈ GV k r, gN g ^ A * ‖F' g‖ ≤ c'` using `fun g hg => by`. Establish `h0` using `hF'.2 [] [] (by simp) (by simp) (by simp) g hg`. Use `first`. Consider the case `exact h0`. Consider the case `simpa [dLR] using h0`.

Consider the case `simpa [dLR, Rw] using h0`. Establish `h1G : (1 : Mat k r) ∈ GV k r` using `by show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules. Establish `hc : 0 ≤ c` using `le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb 1 h1G)`. Establish `hc' : 0 ≤ c'` using `le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb' 1 h1G)`.

Establish `mF : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG` using `aesm_of_continuousOn D.haarG (ckOn_continuousOn hF.1)`. Establish `mF' : AEStronglyMeasurable (fun g : Mt k r => F' (Matrix.of g)) D.μG` using `aesm_of_continuousOn D.haarG (ckOn_continuousOn hF'.1)`. Establish `hx` using `inSS_left D hp`. Establish `hy` using `inSS_right D hp`. Establish `hL` using `hC F F' c c' mF mF' hb hb' _ hx _ hy`.

Establish `hpt : ∀ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ≤ ENNReal.ofReal (hsK Wp Wq) * (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ * ‖F' (Matrix.of g)‖ₑ)`. Introduce `g`. Establish `e1` using `hs_norm_le (rho D p F (Matrix.of g)) (F' (Matrix.of g))`. Establish `e2` using `rho_norm_le D hp F (Matrix.of g)`. Rewrite `e2` using `[sgs_eq]`.

Rewrite using `[← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hK]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Conclude with `e1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (norm_nonneg _)) hK)`. Establish `hlint : (∫⁻ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ∂D.μG) ≤ ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (C * c * c') * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hM : 0 ≤ max C 0 * c * c'` using `mul_nonneg (mul_nonneg (le_max_right _ _) hc) hc'`. Establish `hMx : 0 ≤ max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ)` using `mul_nonneg hM (NNReal.coe_nonneg _)`. Establish `hR : 0 ≤ hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)`. Establish `e : hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) = hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ))` using `by ring`. Rewrite using `[e]`.

Conclude with `mul_nonneg hK (mul_nonneg hMx (NNReal.coe_nonneg _))`. Unfold `Ph`. Use `(norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hR (hlint.trans ?_))` and prove the remaining obligations. Establish `hle : C * c * c' ≤ max C 0 * c * c'` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hc) hc'`. Combine the equalities or inequalities in the displayed calculation.

Establish `h' : ENNReal.ofReal (C * c * c') ≤ ENNReal.ofReal (max C 0 * c * c')` using `ENNReal.ofReal_le_ofReal hle`. Use `gcongr ENNReal.ofReal (hsK Wp Wq) * (?_ * _ * _)`. Use `_ = ENNReal.ofReal (hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) := by`. Rewrite using `[show hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) = hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) by ring, ENNReal.ofReal_mul …`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.phase_function_bound : Formalism.FourierDecayAlt.B.StepPhBound := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hCB
  obtain ⟨C, hC⟩ := hCB
  refine ⟨hsK Wp Wq * max C 0, fun F F' c c' hF hF' p hp => ?_⟩
  have hK : 0 ≤ hsK Wp Wq := hsK_nonneg
  have hb : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c := fun g hg => by
    have h0 := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    first
    | exact h0
    | simpa [dLR] using h0
    | simpa [dLR, Rw] using h0
  have hb' : ∀ g ∈ GV k r, gN g ^ A * ‖F' g‖ ≤ c' := fun g hg => by
    have h0 := hF'.2 [] [] (by simp) (by simp) (by simp) g hg
    first
    | exact h0
    | simpa [dLR] using h0
    | simpa [dLR, Rw] using h0
  have h1G : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hc : 0 ≤ c :=
    le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb 1 h1G)
  have hc' : 0 ≤ c' :=
    le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) (hb' 1 h1G)
  have mF : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG :=
    aesm_of_continuousOn D.haarG (ckOn_continuousOn hF.1)
  have mF' : AEStronglyMeasurable (fun g : Mt k r => F' (Matrix.of g)) D.μG :=
    aesm_of_continuousOn D.haarG (ckOn_continuousOn hF'.1)
  have hx := inSS_left D hp
  have hy := inSS_right D hp
  have hL := hC F F' c c' mF mF' hb hb' _ hx _ hy
  have hpt : ∀ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ≤
      ENNReal.ofReal (hsK Wp Wq) *
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F' (Matrix.of g)‖ₑ) := by
    intro g
    have e1 := hs_norm_le (rho D p F (Matrix.of g)) (F' (Matrix.of g))
    have e2 := rho_norm_le D hp F (Matrix.of g)
    rw [sgs_eq] at e2
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    exact e1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (norm_nonneg _)) hK)
  have hlint : (∫⁻ g : Mt k r, ENNReal.ofReal ‖hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g))‖ ∂D.μG) ≤
      ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (C * c * c') * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) *
        Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
    calc _ ≤ ∫⁻ g : Mt k r, ENNReal.ofReal (hsK Wp Wq) *
            (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
              ‖F' (Matrix.of g)‖ₑ) ∂D.μG := lintegral_mono hpt
      _ = ENNReal.ofReal (hsK Wp Wq) * ∫⁻ g : Mt k r,
            ‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
              ‖F' (Matrix.of g)‖ₑ ∂D.μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hM : 0 ≤ max C 0 * c * c' := mul_nonneg (mul_nonneg (le_max_right _ _) hc) hc'
  have hMx : 0 ≤ max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) :=
    mul_nonneg hM (NNReal.coe_nonneg _)
  have hR : 0 ≤ hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
      (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) := by
    have e : hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
        (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) =
        hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
          (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) := by ring
    rw [e]
    exact mul_nonneg hK (mul_nonneg hMx (NNReal.coe_nonneg _))
  unfold Ph
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hR (hlint.trans ?_))
  have hle : C * c * c' ≤ max C 0 * c * c' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hc) hc'
  calc ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (C * c * c') * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) *
        Ξ (Matrix.of p.2.2 * Matrix.of p.2.1))
      ≤ ENNReal.ofReal (hsK Wp Wq) * (ENNReal.ofReal (max C 0 * c * c') *
          Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
        have h' : ENNReal.ofReal (C * c * c') ≤ ENNReal.ofReal (max C 0 * c * c') := ENNReal.ofReal_le_ofReal hle
        gcongr ENNReal.ofReal (hsK Wp Wq) * (?_ * _ * _)
    _ = ENNReal.ofReal (hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
          (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) := by
        rw [show hsK Wp Wq * max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
            (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ) =
            hsK Wp Wq * (max C 0 * c * c' * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) *
              (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)) by ring,
          ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hMx, ENNReal.ofReal_mul hM,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

section calculus

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k)` using `by omega`. Establish `e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k)` using `by omega`. Simplify using `only [Hpk, if_neg e1, if_neg e2]`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality.

Simplify using `[hi.1, hi.2]`. Establish `e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b)` using `fun h => hb h.2.2.symm`. Rewrite using `[if_neg e3, if_neg hb]`.
-/
private theorem hpk_apply_of_mid_index {k r : ℕ} (i b : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) :
    Hpk k r i b = if b = i then (if i.val = r + k then -1 else 1) else 0 := by
  have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := by omega
  have e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k) := by omega
  simp only [Hpk, if_neg e1, if_neg e2]
  by_cases hb : b = i
  · subst hb
    simp [hi.1, hi.2]
  · have e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b) := fun h => hb h.2.2.symm
    rw [if_neg e3, if_neg hb]

/- English proof (translation)
Establish `hi1` using `i.isLt`. Establish `hb1` using `b.isLt`. Establish `e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b)` using `fun h => hi ⟨h.1, h.2.1⟩`. Distinguish the cases in `hb : b.val = 2 * r + k - i.val`. Rewrite using `[if_pos hb]`.

Distinguish the cases in `h1 : i.val < r`. Establish `e1 : i.val < r ∧ i.val + b.val = 2 * r + k` using `⟨h1, by omega⟩`. Simplify using `only [Hpk, if_pos e1]`. Establish `e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k)` using `fun h => h1 h.1`. Establish `e2 : b.val < r ∧ i.val + b.val = 2 * r + k` using `by omega`.

Simplify using `only [Hpk, if_neg e1, if_pos e2]`. Rewrite using `[if_neg hb]`. Establish `e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k)` using `by omega`. Establish `e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k)` using `by omega`. Simplify using `only [Hpk, if_neg e1, if_neg e2, if_neg e3]`.
-/
private theorem hpk_apply_of_not_mid_index {k r : ℕ} (i b : Fin (2 * r + k + 1)) (hi : ¬(r ≤ i.val ∧ i.val ≤ r + k)) :
    Hpk k r i b = if b.val = 2 * r + k - i.val then 1 else 0 := by
  have hi1 := i.isLt
  have hb1 := b.isLt
  have e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b) := fun h => hi ⟨h.1, h.2.1⟩
  by_cases hb : b.val = 2 * r + k - i.val
  · rw [if_pos hb]
    by_cases h1 : i.val < r
    · have e1 : i.val < r ∧ i.val + b.val = 2 * r + k := ⟨h1, by omega⟩
      simp only [Hpk, if_pos e1]
    · have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := fun h => h1 h.1
      have e2 : b.val < r ∧ i.val + b.val = 2 * r + k := by omega
      simp only [Hpk, if_neg e1, if_pos e2]
  · rw [if_neg hb]
    have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := by omega
    have e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k) := by omega
    simp only [Hpk, if_neg e1, if_neg e2, if_neg e3]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hi1` using `i.isLt`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Rewrite using `[Finset.sum_eq_single i]`.

Rewrite using `[hpk_apply_of_mid_index i i hi, hpk_apply_of_mid_index i j hi, if_pos rfl]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Rewrite using `[if_neg (Ne.symm hij), if_neg hij, mul_zero]`. Introduce `b _ hb`. Rewrite using `[hpk_apply_of_mid_index i b hi, if_neg hb, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hn : 2 * r + k - i.val < 2 * r + k + 1` using `by omega`. Establish `hσ : ¬(r ≤ (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ∧ (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ≤ r + k)` using `by show ¬(r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)`. Use linear arithmetic over natural numbers and integers. Establish `hσσ : 2 * r + k - (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val = i.val` using `by show 2 * r + k - (2 * r + k - i.val) = i.val`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.sum_eq_single ⟨2 * r + k - i.val, hn⟩]`. Rewrite using `[hpk_apply_of_not_mid_index i _ hi, hpk_apply_of_not_mid_index _ j hσ, if_pos rfl, one_mul, hσσ]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hij, if_neg (fun h => hij (Fin.ext h.symm))]`. Introduce `b _ hb`. Establish `hb' : ¬ b.val = 2 * r + k - i.val` using `fun h => hb (Fin.ext h)`. Rewrite using `[hpk_apply_of_not_mid_index i b hi, if_neg hb', zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem hpk_mul_self' {k r : ℕ} : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi1 := i.isLt
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · rw [hpk_apply_of_mid_index i i hi, hpk_apply_of_mid_index i j hi, if_pos rfl]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        split_ifs <;> norm_num
      · rw [if_neg (Ne.symm hij), if_neg hij, mul_zero]
    · intro b _ hb
      rw [hpk_apply_of_mid_index i b hi, if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · have hn : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hσ : ¬(r ≤ (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ∧
        (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ≤ r + k) := by
      show ¬(r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)
      omega
    have hσσ : 2 * r + k - (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val = i.val := by
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hn⟩]
    · rw [hpk_apply_of_not_mid_index i _ hi, hpk_apply_of_not_mid_index _ j hσ, if_pos rfl, one_mul, hσσ]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.ext h.symm))]
    · intro b _ hb
      have hb' : ¬ b.val = 2 * r + k - i.val := fun h => hb (Fin.ext h)
      rw [hpk_apply_of_not_mid_index i b hi, if_neg hb', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hH : Hpk k r * Hpk k r = 1` using `hpk_mul_self'`. Establish `hdet : (Hpk k r).det * (Hpk k r).det = 1` using `by rw [← Matrix.det_mul, hH, Matrix.det_one]`. Establish `hu : IsUnit (Hpk k r)` using `by first`. Consider the case `exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hH)`. Consider the case `exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_eq_one _ _ hdet)`.

Consider the case `exact (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.of_mul_eq_one _ hdet)`. Consider the case `exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one hdet))`. Establish `hinv : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_left_inv hH`. Establish `e : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left hX`. Establish `hXh : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹`.

Rewrite using `[hinv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : ((t : ℂ) • X)ᴴ = Hpk k r * ((t : ℂ) • -X) * (Hpk k r)⁻¹`. Rewrite using `[Matrix.conjTranspose_smul, hXh, Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`.

Conclude with `Complex.conj_ofReal t`. Establish `hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (((t : ℂ) • X)ᴴ)` using `by first`. Consider the case `exact (Matrix.exp_conjTranspose _).symm`. Consider the case `exact Matrix.exp_conjTranspose _`. Establish `hEE : NormedSpace.exp ((t : ℂ) • -X) * NormedSpace.exp ((t : ℂ) • X) = 1`.

Rewrite using `[smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left), neg_add_cancel, NormedSpace.exp_zero]`. Use `show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r`. Rewrite using `[hE, hs, Matrix.exp_conj _ _ hu, hinv, Matrix.mul_assoc (Hpk k r * _) (Hpk k r), hH, Matrix.mul_one, Matrix.mul_assoc, hEE, Matrix.mul_one]`.
-/
theorem exp_mem {X : Mat k r} (hX : inLie k r X) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := by
  have hH : Hpk k r * Hpk k r = 1 := hpk_mul_self'
  have hdet : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, hH, Matrix.det_one]
  have hu : IsUnit (Hpk k r) := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hH)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_eq_one _ _ hdet)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.of_mul_eq_one _ hdet)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one hdet))
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH
  have e : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hXh : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [e, Matrix.mul_neg]
  have hs : ((t : ℂ) • X)ᴴ = Hpk k r * ((t : ℂ) • -X) * (Hpk k r)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact Complex.conj_ofReal t
  have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (((t : ℂ) • X)ᴴ) := by
    first
    | exact (Matrix.exp_conjTranspose _).symm
    | exact Matrix.exp_conjTranspose _
  have hEE : NormedSpace.exp ((t : ℂ) • -X) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
  rw [hE, hs, Matrix.exp_conj _ _ hu, hinv, Matrix.mul_assoc (Hpk k r * _) (Hpk k r), hH, Matrix.mul_one,
    Matrix.mul_assoc, hEE, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Complex.ofReal_add, add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)`.
-/
theorem exp_add' (X : Mat k r) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

/- English proof (translation)
Simplify using `[NormedSpace.exp_zero]`.
-/
theorem curve_zero (g X : Mat k r) : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp [NormedSpace.exp_zero]

/- English proof (translation)
Conclude with `mul_mem_uh hg (exp_mem hX t)`.
-/
theorem curve_mem {g X : Mat k r} (hg : g ∈ GV k r) (hX : inLie k r X) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := by
  exact mul_mem_uh hg (exp_mem hX t)

/- English proof (translation)
Establish `h` using `hasDerivAt_mul_exp_smul_zero (g * NormedSpace.exp ((t₀ : ℂ) • X)) X`. Rewrite `h` using `[← sub_self t₀]`. Establish `h2` using `HasDerivAt.comp_sub_const t₀ t₀ h`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show g * NormedSpace.exp ((t : ℂ) • X) = g * NormedSpace.exp ((t₀ : ℂ) • X) * NormedSpace.exp (((t - t₀ : ℝ) : ℂ) • X)`.

Establish `e : t₀ + (t - t₀) = t` using `by ring`. Rewrite using `[Matrix.mul_assoc, ← exp_add', e]`.
-/
theorem curve_hasDerivAt (g X : Mat k r) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * NormedSpace.exp ((t₀ : ℂ) • X) * X) t₀ := by
  have h := hasDerivAt_mul_exp_smul_zero (g * NormedSpace.exp ((t₀ : ℂ) • X)) X
  rw [← sub_self t₀] at h
  have h2 := HasDerivAt.comp_sub_const t₀ t₀ h
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show g * NormedSpace.exp ((t : ℂ) • X) =
    g * NormedSpace.exp ((t₀ : ℂ) • X) * NormedSpace.exp (((t - t₀ : ℝ) : ℂ) • X)
  have e : t₀ + (t - t₀) = t := by ring
  rw [Matrix.mul_assoc, ← exp_add', e]

/- English proof (translation)
Rewrite using `[contDiff_one_iff_deriv]`. Establish `hd : Differentiable ℝ (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X))` using `fun t => (curve_hasDerivAt g X t).differentiableAt`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun t : ℝ => mulRightRealCLM X (g * NormedSpace.exp ((t : ℂ) • X))` using `(mulRightRealCLM X).continuous.comp hd.continuous`. Conclude with `(continuous_congr fun t => (curve_hasDerivAt g X t).deriv).2 hc`.
-/
theorem curve_contDiff (g X : Mat k r) : ContDiff ℝ 1 (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
  rw [contDiff_one_iff_deriv]
  have hd : Differentiable ℝ (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    fun t => (curve_hasDerivAt g X t).differentiableAt
  refine ⟨hd, ?_⟩
  have hc : Continuous fun t : ℝ => mulRightRealCLM X (g * NormedSpace.exp ((t : ℂ) • X)) :=
    (mulRightRealCLM X).continuous.comp hd.continuous
  exact (continuous_congr fun t => (curve_hasDerivAt g X t).deriv).2 hc

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg, hf', he⟩` from `h g₀ hg₀`. Conclude with `⟨U, f', hU, hg, hf'.of_le (by exact_mod_cast hmm), he⟩`.
-/
theorem ckOn_mono {m m' : ℕ∞} (hmm : m ≤ m') {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn m' UU f) :
    CkOn m UU f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hg, hf'.of_le (by exact_mod_cast hmm), he⟩

/- English proof (translation)
Establish `hc` using `curve_hasDerivAt g X 0`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hc`. Establish `hf'' : HasFDerivAt f' (fderiv ℝ f' g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[curve_zero]`. Conclude with `hf'.hasFDerivAt`.

Establish `hcomp` using `hf''.comp_hasDerivAt (0 : ℝ) hc`. Apply `hcomp.congr_of_eventuallyEq` to reduce the goal to its premises. Establish `hU' : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U`. Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[curve_zero]`.

Conclude with `hU.mem_nhds hg`. Use `filter_upwards [hU'] with t ht`. Conclude with `he _ ht (curve_mem hgG hX t)`.
-/
theorem hasDerivAt_of_ext {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r}
    (hg : g ∈ U) (hgG : g ∈ GV k r) (hX : inLie k r X) (hf' : DifferentiableAt ℝ f' g)
    (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ f' g (g * X)) 0 := by
  have hc := curve_hasDerivAt g X 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hc
  have hf'' : HasFDerivAt f' (fderiv ℝ f' g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [curve_zero]
    exact hf'.hasFDerivAt
  have hcomp := hf''.comp_hasDerivAt (0 : ℝ) hc
  apply hcomp.congr_of_eventuallyEq
  have hU' : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hU'] with t ht
  exact he _ ht (curve_mem hgG hX t)

/- English proof (translation)
Take `⟨U, f', hU, hgU, hf', he⟩` from `h g hg`. Establish `hd : DifferentiableAt ℝ f' g` using `(hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Establish `hh` using `hasDerivAt_of_ext hU hgU hg hX hd he`. Conclude with `hh.differentiableAt.hasDerivAt`.
-/
theorem rdV_hasDerivAt {f : Mat k r → E} (h : CkOn 1 (GV k r) f) {g X : Mat k r} (hg : g ∈ GV k r)
    (hX : inLie k r X) : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hh := hasDerivAt_of_ext hU hgU hg hX hd he
  exact hh.differentiableAt.hasDerivAt

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hf', he⟩` from `h g₀ hg₀`. Use `⟨U, fun g => fderiv ℝ f' g (g * X), hU, hgU, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g : Mat k r => g * X) U` using `(LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff.contDiffOn`. Conclude with `(hf'.fderiv_of_isOpen hU (m := (m : WithTop ℕ∞)) (le_of_eq (by norm_cast))).clm_apply h2`.

Introduce `g hg hgG`. Establish `hd : DifferentiableAt ℝ f' g` using `(hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Conclude with `(hasDerivAt_of_ext hU hg hgG hX hd he).deriv`.
-/
theorem ckOn_RdV {m : ℕ∞} {f : Mat k r → E} {X : Mat k r} (hX : inLie k r X) (h : CkOn (m + 1) (GV k r) f) :
    CkOn m (GV k r) (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (g * X), hU, hgU, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g : Mat k r => g * X) U :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff.contDiffOn
    exact (hf'.fderiv_of_isOpen hU (m := (m : WithTop ℕ∞)) (le_of_eq (by norm_cast))).clm_apply h2
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_of_ext hU hg hgG hX hd he).deriv

/- English proof (translation)
Proceed by induction on `w generalizing m with`. Consider the case `nil`. Establish `hmN : m ≤ N` using `by simpa using hle`. Conclude with `ckOn_mono (by exact_mod_cast hmN) h`. Consider the case `cons X w ih`.

Establish `hX : inLie k r X` using `hw X (by simp)`. Establish `hw' : ∀ Y ∈ w, inLie k r Y` using `fun Y hY => hw Y (by simp [hY])`. Establish `hle' : m + 1 + w.length ≤ N` using `by simp at hle; omega`. Establish `h1 : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) (Rw w f)` using `ih hw' (m + 1) hle'`. Move the coercions through the operations in `at h1`.

Conclude with `ckOn_RdV hX h1`.
-/
theorem ckOn_Rw {f : Mat k r → E} {N : ℕ} (h : CkOn (N : ℕ∞) (GV k r) f) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : CkOn (m : ℕ∞) (GV k r) (Rw w f) := by
  induction w generalizing m with
  | nil =>
    have hmN : m ≤ N := by simpa using hle
    exact ckOn_mono (by exact_mod_cast hmN) h
  | cons X w ih =>
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (by simp [hY])
    have hle' : m + 1 + w.length ≤ N := by simp at hle; omega
    have h1 : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) (Rw w f) := ih hw' (m + 1) hle'
    push_cast at h1
    exact ckOn_RdV hX h1

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t₀`. Establish `hm` using `curve_mem hg hX t₀`. Take `⟨U, f', hU, hgU, hf', he⟩` from `h _ hm`. Establish `hcd : ContDiffAt ℝ 1 (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) t₀` using `(curve_contDiff g X).contDiffAt`.

Establish `hf'a : ContDiffAt ℝ 1 f' (g * NormedSpace.exp ((t₀ : ℂ) • X))` using `hf'.contDiffAt (hU.mem_nhds hgU)`. Establish `hcomp` using `hf'a.comp t₀ hcd`. Apply `hcomp.congr_of_eventuallyEq` to reduce the goal to its premises. Establish `hU' : ∀ᶠ t : ℝ in 𝓝 t₀, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hcd.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)`. Use `filter_upwards [hU'] with t ht`.

Conclude with `he _ ht (curve_mem hg hX t)`.
-/
theorem ckOn_curve {f : Mat k r → E} (h : CkOn 1 (GV k r) f) {g X : Mat k r} (hg : g ∈ GV k r)
    (hX : inLie k r X) : ContDiff ℝ 1 (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  have hm := curve_mem hg hX t₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h _ hm
  have hcd : ContDiffAt ℝ 1 (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) t₀ :=
    (curve_contDiff g X).contDiffAt
  have hf'a : ContDiffAt ℝ 1 f' (g * NormedSpace.exp ((t₀ : ℂ) • X)) := hf'.contDiffAt (hU.mem_nhds hgU)
  have hcomp := hf'a.comp t₀ hcd
  apply hcomp.congr_of_eventuallyEq
  have hU' : ∀ᶠ t : ℝ in 𝓝 t₀, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hcd.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hU'] with t ht
  exact he _ ht (curve_mem hg hX t)

def mulLc (a : Mat k r) : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

/- English proof (translation)
Introduce `g₀ hg₀`. Establish `hmem : ∀ g ∈ GV k r, a * g * b ∈ GV k r` using `fun g hg => mul_mem_uh (mul_mem_uh ha hg) hb`. Take `⟨U, f', hU, hgU, hf', he⟩` from `h _ (hmem g₀ hg₀)`. Use `set ψ : Mat k r →L[ℝ] Mat k r := (mulLc a).comp (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ b)) with hψ`. Establish `hψa : ∀ g, ψ g = a * g * b` using `fun g => by simp [hψ, mulLc, Matrix.mul_assoc]`.

Use `⟨ψ ⁻¹' U, fun g => f' (ψ g), hU.preimage ψ.continuous, by simpa [hψa] using hgU, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hf'.comp ψ.contDiff.contDiffOn (fun x hx => hx)`. Introduce `g hg hgG`. Simplify using `only [Set.mem_preimage, hψa] at hg ⊢`. Conclude with `he _ hg (hmem g hgG)`.
-/
theorem ckOn_translate {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) {a b : Mat k r} (ha : a ∈ GV k r)
    (hb : b ∈ GV k r) : CkOn m (GV k r) (fun g => f (a * g * b)) := by
  intro g₀ hg₀
  have hmem : ∀ g ∈ GV k r, a * g * b ∈ GV k r := fun g hg => mul_mem_uh (mul_mem_uh ha hg) hb
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h _ (hmem g₀ hg₀)
  set ψ : Mat k r →L[ℝ] Mat k r :=
    (mulLc a).comp (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ b)) with hψ
  have hψa : ∀ g, ψ g = a * g * b := fun g => by simp [hψ, mulLc, Matrix.mul_assoc]
  refine ⟨ψ ⁻¹' U, fun g => f' (ψ g), hU.preimage ψ.continuous, by simpa [hψa] using hgU, ?_, ?_⟩
  · exact hf'.comp ψ.contDiff.contDiffOn (fun x hx => hx)
  · intro g hg hgG
    simp only [Set.mem_preimage, hψa] at hg ⊢
    exact he _ hg (hmem g hgG)

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg, hf', he⟩` from `h g₀ hg₀`. Use `⟨U, fun x => L (f' x), hU, hg, ?_, fun g hgU hgG => by simp only [he g hgU hgG]⟩` and prove the remaining obligations. Conclude with `(L.restrictScalars ℝ).contDiff.comp_contDiffOn hf'`.
-/
theorem ckOn_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {m : ℕ∞} {f : Mat k r → E}
    (h : CkOn m (GV k r) f) (L : E →L[ℂ] E') : CkOn m (GV k r) (fun g => L (f g)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun x => L (f' x), hU, hg, ?_, fun g hgU hgG => by simp only [he g hgU hgG]⟩
  exact (L.restrictScalars ℝ).contDiff.comp_contDiffOn hf'

/- English proof (translation)
Introduce `g₀ hg₀`. Distinguish the cases in `hc : g₀ ∈ closure {g | g ∈ GV k r ∧ φ g ≠ 0}`. Take `⟨U1, a', hU1, hg1, ha', he1⟩` from `ha g₀ (hs hc)`. Take `⟨U2, φ', hU2, hg2, hφ', he2⟩` from `hφ g₀ hg₀`. Use `⟨U1 ∩ U2, fun x => a' x (φ' x), hU1.inter hU2, ⟨hg1, hg2⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hR : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ (a' x)) (U1 ∩ U2)` using `(ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff.comp_contDiffOn ((ha'.mono Set.inter_subset_left).of_le (by exact_mod_cast le_top))`. Conclude with `hR.clm_apply (hφ'.mono Set.inter_subset_right)`. Introduce `g hg hgG`. Simplify using `only [he1 g hg.1 hgG, he2 g hg.2 hgG]`. Use `⟨(closure {g | g ∈ GV k r ∧ φ g ≠ 0})ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hc, contDiffOn_const, ?_⟩` and prove the remaining obligations.

Introduce `g hg hgG`. Establish `hz : φ g = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hg (subset_closure ⟨hgG, hne⟩)`. Simplify using `[hz]`.
-/
theorem ckOn_coef {m : ℕ∞} {UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E)} {φ : Mat k r → E}
    (ha : CkOn ⊤ UU a) (hφ : CkOn m (GV k r) φ) (hs : closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ UU) :
    CkOn m (GV k r) (fun x => a x (φ x)) := by
  intro g₀ hg₀
  by_cases hc : g₀ ∈ closure {g | g ∈ GV k r ∧ φ g ≠ 0}
  · obtain ⟨U1, a', hU1, hg1, ha', he1⟩ := ha g₀ (hs hc)
    obtain ⟨U2, φ', hU2, hg2, hφ', he2⟩ := hφ g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => a' x (φ' x), hU1.inter hU2, ⟨hg1, hg2⟩, ?_, ?_⟩
    · have hR : ContDiffOn ℝ (m : WithTop ℕ∞)
          (fun x => ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ (a' x)) (U1 ∩ U2) :=
        (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff.comp_contDiffOn
          ((ha'.mono Set.inter_subset_left).of_le (by exact_mod_cast le_top))
      exact hR.clm_apply (hφ'.mono Set.inter_subset_right)
    · intro g hg hgG
      simp only [he1 g hg.1 hgG, he2 g hg.2 hgG]
  · refine ⟨(closure {g | g ∈ GV k r ∧ φ g ≠ 0})ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hc,
      contDiffOn_const, ?_⟩
    intro g hg hgG
    have hz : φ g = 0 := by
      by_contra hne
      exact hg (subset_closure ⟨hgG, hne⟩)
    simp [hz]

end calculus

section adj

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hc : ContinuousOn (fun x => hsInner (A x) (B x)) (GV k r)` using `hs_continuous.comp_continuousOn (hA.prodMk hB)`. Use `(h.const_mul (hsK Wp Wq)).mono' (aesm_of_continuousOn D.haarG hc) (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hs_integrable (D : RealPlaceData k r Wp Wq) {A B : Mat k r → (Wq →L[ℂ] Wp)}
    (hA : ContinuousOn A (GV k r)) (hB : ContinuousOn B (GV k r))
    (h : Integrable (fun g : Mt k r => ‖B (Matrix.of g)‖ * ‖A (Matrix.of g)‖) D.μG) :
    Integrable (fun g : Mt k r => hsInner (A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hc : ContinuousOn (fun x => hsInner (A x) (B x)) (GV k r) :=
    hs_continuous.comp_continuousOn (hA.prodMk hB)
  refine (h.const_mul (hsK Wp Wq)).mono' (aesm_of_continuousOn D.haarG hc) (ae_of_all _ fun g => ?_)
  calc ‖hsInner (A (Matrix.of g)) (B (Matrix.of g))‖
      ≤ hsK Wp Wq * (‖A (Matrix.of g)‖ * ‖B (Matrix.of g)‖) := hs_norm_le _ _
    _ = hsK Wp Wq * (‖B (Matrix.of g)‖ * ‖A (Matrix.of g)‖) := by ring

/- English proof (translation)
Establish `hA : HasDerivAt (fun t => hsVec (a t)) (hsVec a') x`. Use `((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x ha` as an intermediate fact. Simplify `this` using `[Function.comp_def, hsL_apply]`. Establish `hB : HasDerivAt (fun t => hsVec (b t)) (hsVec b') x`. Use `((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hb` as an intermediate fact.

Simplify `this` using `[Function.comp_def, hsL_apply]`. Simplify `HasDerivAt.inner ℂ hB hA` using `only [hsInner]`.
-/
theorem hs_hasDerivAt {a b : ℝ → (Wq →L[ℂ] Wp)} {a' b' : Wq →L[ℂ] Wp} {x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) :
    HasDerivAt (fun t => hsInner (a t) (b t)) (hsInner a' (b x) + hsInner (a x) b') x := by
  have hA : HasDerivAt (fun t => hsVec (a t)) (hsVec a') x := by
    have := ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x ha
    simpa [Function.comp_def, hsL_apply] using this
  have hB : HasDerivAt (fun t => hsVec (b t)) (hsVec b') x := by
    have := ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hb
    simpa [Function.comp_def, hsL_apply] using this
  simpa only [hsInner] using HasDerivAt.inner ℂ hB hA

/- English proof (translation)
Establish `hA : ContDiff ℝ 1 (fun t => hsVec (a t))`. Simplify `((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp ha` using `[Function.comp_def, hsL_apply]`. Establish `hB : ContDiff ℝ 1 (fun t => hsVec (b t))`. Simplify `((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp hb` using `[Function.comp_def, hsL_apply]`. Simplify `hB.inner ℂ hA` using `only [hsInner]`.
-/
theorem hs_contDiff {a b : ℝ → (Wq →L[ℂ] Wp)} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (fun t => hsInner (a t) (b t)) := by
  have hA : ContDiff ℝ 1 (fun t => hsVec (a t)) := by
    simpa [Function.comp_def, hsL_apply] using
      ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp ha
  have hB : ContDiff ℝ 1 (fun t => hsVec (b t)) := by
    simpa [Function.comp_def, hsL_apply] using
      ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp hb
  simpa only [hsInner] using hB.inner ℂ hA

/- English proof (translation)
Use `haveI := haar_sigmaFinite D.haarG`. Use `set h : Mat k r → ℂ := fun g => hsInner (f1 g) (f2 g) with hh`. Establish `hR : ∀ g ∈ GV k r, RdV X h g = hsInner (RdV X f1 g) (f2 g) + hsInner (f1 g) (RdV X f2 g)`. Introduce `g hg`. Establish `H` using `hs_hasDerivAt (rdV_hasDerivAt h1 hg hX) (rdV_hasDerivAt h2 hg hX)`.

Simplify using `only [curve_zero] at H`. Conclude with `H.deriv`. Establish `hae : ∀ᵐ g ∂D.μG, RdV X h (Matrix.of g) = hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) + hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g))` using `by filter_upwards [haar_ae D.haarG] with g hg`. Conclude with `hR _ hg`. Establish `hinv : ∀ t : ℝ, D.μG.map (rmulF (NormedSpace.exp ((t : ℂ) • X))) = D.μG` using `fun t => D.haarG.right _ (exp_mem hX t)`.

Establish `hcd : ∀ᵐ g ∂D.μG, ContDiff ℝ 1 fun t : ℝ => h (Matrix.of g * NormedSpace.exp ((t : ℂ) • X))` using `by filter_upwards [haar_ae D.haarG] with g hg`. Conclude with `hs_contDiff (ckOn_curve h1 hg hX) (ckOn_curve h2 hg hX)`. Establish `hI : Integrable (fun g : Mt k r => RdV X h (Matrix.of g)) D.μG`. Use `(i1.add i2).congr ?_` and prove the remaining obligations. Use `filter_upwards [hae] with g hg`.

Rewrite using `[hg]`. Both sides reduce to the same expression. Establish `hz` using `Formalism.FourierDecayAlt.P.B1.intZero _ D.μG X h hinv hcd i0 hI`. Establish `hsplit : (∫ g : Mt k r, RdV X h (Matrix.of g) ∂D.μG) = (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) + ∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG`. Rewrite using `[integral_congr_ae hae, integral_add i1 i2]`.

Rewrite `hsplit` using `[hz]`. Take the linear combination `(-1 : ℂ) * hsplit`.
-/
theorem ibp (D : RealPlaceData k r Wp Wq) {X : Mat k r} (hX : inLie k r X) {f1 f2 : Mat k r → (Wq →L[ℂ] Wp)}
    (h1 : CkOn 1 (GV k r) f1) (h2 : CkOn 1 (GV k r) f2)
    (i0 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i1 : Integrable (fun g : Mt k r => hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g))) D.μG)
    (i2 : Integrable (fun g : Mt k r => hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g))) D.μG) :
    (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) =
      -∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG := by
  haveI := haar_sigmaFinite D.haarG
  set h : Mat k r → ℂ := fun g => hsInner (f1 g) (f2 g) with hh
  have hR : ∀ g ∈ GV k r, RdV X h g = hsInner (RdV X f1 g) (f2 g) + hsInner (f1 g) (RdV X f2 g) := by
    intro g hg
    have H := hs_hasDerivAt (rdV_hasDerivAt h1 hg hX) (rdV_hasDerivAt h2 hg hX)
    simp only [curve_zero] at H
    exact H.deriv
  have hae : ∀ᵐ g ∂D.μG, RdV X h (Matrix.of g) =
      hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) +
        hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) := by
    filter_upwards [haar_ae D.haarG] with g hg
    exact hR _ hg
  have hinv : ∀ t : ℝ, D.μG.map (rmulF (NormedSpace.exp ((t : ℂ) • X))) = D.μG :=
    fun t => D.haarG.right _ (exp_mem hX t)
  have hcd : ∀ᵐ g ∂D.μG, ContDiff ℝ 1 fun t : ℝ => h (Matrix.of g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [haar_ae D.haarG] with g hg
    exact hs_contDiff (ckOn_curve h1 hg hX) (ckOn_curve h2 hg hX)
  have hI : Integrable (fun g : Mt k r => RdV X h (Matrix.of g)) D.μG := by
    refine (i1.add i2).congr ?_
    filter_upwards [hae] with g hg
    rw [hg]
    rfl
  have hz := Formalism.FourierDecayAlt.P.B1.intZero _ D.μG X h hinv hcd i0 hI
  have hsplit : (∫ g : Mt k r, RdV X h (Matrix.of g) ∂D.μG) =
      (∫ g : Mt k r, hsInner (RdV X f1 (Matrix.of g)) (f2 (Matrix.of g)) ∂D.μG) +
        ∫ g : Mt k r, hsInner (f1 (Matrix.of g)) (RdV X f2 (Matrix.of g)) ∂D.μG := by
    rw [integral_congr_ae hae, integral_add i1 i2]
  rw [hz] at hsplit
  linear_combination (-1 : ℂ) * hsplit

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [List.drop_zero, List.take_zero, List.reverse_nil, pow_zero, one_mul]`. Both sides reduce to the same expression. Consider the case `succ j ih`.

Establish `hjl : j < w.length` using `by omega`. Establish `hX : inLie k r w[j]` using `hw _ (List.getElem_mem hjl)`. Establish `hd : w.drop j = w[j] :: w.drop (j + 1)` using `List.drop_eq_getElem_cons hjl`. Establish `ht : (w.take (j + 1)).reverse = w[j] :: (w.take j).reverse`. Rewrite using `[List.take_succ, List.getElem?_eq_getElem hjl]`.

Simplify using the standard rewrite rules. Establish `hwd : ∀ Y ∈ w.drop (j + 1), inLie k r Y` using `fun Y hY => hw Y (List.mem_of_mem_drop hY)`. Establish `hwt : ∀ Y ∈ (w.take j).reverse, inLie k r Y` using `fun Y hY => hw Y (List.mem_of_mem_take (List.mem_reverse.1 hY))`. Establish `h1 : CkOn 1 (GV k r) (Rw (w.drop (j + 1)) f)`. Establish `h0` using `ckOn_Rw hf (w.drop (j + 1)) hwd 1 (by simp; omega)`.

Conclude with `h0` after adjusting the coercions. Establish `h2 : CkOn 1 (GV k r) (Rw (w.take j).reverse φ)`. Establish `h0` using `ckOn_Rw hφ ((w.take j).reverse) hwt 1 (by simp; omega)`. Conclude with `h0` after adjusting the coercions. Establish `c1` using `ckOn_continuousOn h1`.

Establish `c2` using `ckOn_continuousOn h2`. Establish `c3` using `ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h1))`. Establish `c4` using `ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h2))`. Establish `i0` using `hs_integrable D c1 c2 (hI j (j + 1) (by omega) (by omega))`. Establish `hI1` using `hI j j le_rfl (by omega)`.

Rewrite `hI1` using `[hd]`. Establish `i1` using `hs_integrable D c3 c2 hI1`. Establish `hI2` using `hI (j + 1) (j + 1) le_rfl (by omega)`. Rewrite `hI2` using `[ht]`. Establish `i2` using `hs_integrable D c1 c4 hI2`.

Establish `key` using `ibp D hX h1 h2 i0 i1 i2`. Rewrite using `[ih (by omega), hd, ht]`. Establish `key' : (∫ g : Mt k r, hsInner (Rw (w[j] :: w.drop (j + 1)) f (Matrix.of g)) (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG) = -∫ g : Mt k r, hsInner (Rw (w.drop (j + 1)) f (Matrix.of g)) (Rw (w[j] :: (w.take j).reverse) φ (Matrix.of g)) ∂D.μG` using `key`. Rewrite using `[key']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem word_adj (D : RealPlaceData k r Wp Wq) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) {N : ℕ}
    (hN : w.length + 1 ≤ N) {f φ : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn (N : ℕ∞) (GV k r) f)
    (hφ : CkOn (N : ℕ∞) (GV k r) φ)
    (hI : ∀ i j : ℕ, i ≤ j → j ≤ w.length → Integrable (fun g : Mt k r =>
      ‖Rw (w.take i).reverse φ (Matrix.of g)‖ * ‖Rw (w.drop j) f (Matrix.of g)‖) D.μG)
    (j : ℕ) (hj : j ≤ w.length) :
    (∫ g : Mt k r, hsInner (Rw w f (Matrix.of g)) (φ (Matrix.of g)) ∂D.μG) =
      (-1) ^ j * ∫ g : Mt k r, hsInner (Rw (w.drop j) f (Matrix.of g))
        (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG := by
  induction j with
  | zero =>
    simp only [List.drop_zero, List.take_zero, List.reverse_nil, pow_zero, one_mul]
    rfl
  | succ j ih =>
    have hjl : j < w.length := by omega
    have hX : inLie k r w[j] := hw _ (List.getElem_mem hjl)
    have hd : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have ht : (w.take (j + 1)).reverse = w[j] :: (w.take j).reverse := by
      rw [List.take_succ, List.getElem?_eq_getElem hjl]
      simp
    have hwd : ∀ Y ∈ w.drop (j + 1), inLie k r Y := fun Y hY => hw Y (List.mem_of_mem_drop hY)
    have hwt : ∀ Y ∈ (w.take j).reverse, inLie k r Y :=
      fun Y hY => hw Y (List.mem_of_mem_take (List.mem_reverse.1 hY))
    have h1 : CkOn 1 (GV k r) (Rw (w.drop (j + 1)) f) := by
      have h0 := ckOn_Rw hf (w.drop (j + 1)) hwd 1 (by simp; omega)
      exact_mod_cast h0
    have h2 : CkOn 1 (GV k r) (Rw (w.take j).reverse φ) := by
      have h0 := ckOn_Rw hφ ((w.take j).reverse) hwt 1 (by simp; omega)
      exact_mod_cast h0
    have c1 := ckOn_continuousOn h1
    have c2 := ckOn_continuousOn h2
    have c3 := ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h1))
    have c4 := ckOn_continuousOn (ckOn_RdV (m := 0) hX (by simpa using h2))
    have i0 := hs_integrable D c1 c2 (hI j (j + 1) (by omega) (by omega))
    have hI1 := hI j j le_rfl (by omega)
    rw [hd] at hI1
    have i1 := hs_integrable D c3 c2 hI1
    have hI2 := hI (j + 1) (j + 1) le_rfl (by omega)
    rw [ht] at hI2
    have i2 := hs_integrable D c1 c4 hI2
    have key := ibp D hX h1 h2 i0 i1 i2
    rw [ih (by omega), hd, ht]
    have key' : (∫ g : Mt k r, hsInner (Rw (w[j] :: w.drop (j + 1)) f (Matrix.of g))
        (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG) =
        -∫ g : Mt k r, hsInner (Rw (w.drop (j + 1)) f (Matrix.of g))
          (Rw (w[j] :: (w.take j).reverse) φ (Matrix.of g)) ∂D.μG := key
    rw [key']
    ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [hs_zero_left]`. Consider the case `cons x l ih => simp [hs_add_left, ih]`.
-/
theorem hs_listSum_left {ι : Type*} (l : List ι) (a : ι → (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsInner ((l.map a).sum) B = (l.map fun T => hsInner (a T) B).sum := by
  induction l with
  | nil => simp [hs_zero_left]
  | cons x l ih => simp [hs_add_left, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [hs_zero_right]`. Consider the case `cons x l ih => simp [hs_add_right, ih]`.
-/
theorem hs_listSum_right {ι : Type*} (l : List ι) (a : ι → (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsInner B ((l.map a).sum) = (l.map fun T => hsInner B (a T)).sum := by
  induction l with
  | nil => simp [hs_zero_right]
  | cons x l ih => simp [hs_add_right, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons T l ih`. Establish `hT` using `h T (by simp)`. Take `⟨ih1, ih2⟩` from `ih (fun T' hT' => h T' (by simp [hT']))`.

Simplify using `only [List.map_cons, List.sum_cons]`. Conclude with `⟨hT.add ih1, by rw [integral_add hT ih1, ih2]⟩`.
-/
theorem integral_listSum {ι α : Type*} [MeasurableSpace α] (μ : Measure α) (l : List ι) (φ : ι → α → ℂ)
    (h : ∀ T ∈ l, Integrable (φ T) μ) :
    Integrable (fun g => (l.map fun T => φ T g).sum) μ ∧
      (∫ g, (l.map fun T => φ T g).sum ∂μ) = (l.map fun T => ∫ g, φ T g ∂μ).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    have hT := h T (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun T' hT' => h T' (by simp [hT']))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hT.add ih1, by rw [integral_add hT ih1, ih2]⟩

/- English proof (translation)
Unfold `opOrder`. Proceed by induction on `Θ with`. Consider the case `nil => simp at hT`. Consider the case `cons T' Θ ih`. Simplify using `only [List.map_cons, List.foldr_cons]`.

Break down `List.mem_cons.1 hT with rfl | h` into its components or cases. Conclude with `le_max_left _ _`. Conclude with `le_trans (ih h) (le_max_right _ _)`.
-/
theorem len_le_order (Θ : DiffOp k r Wp Wq) {T : DTerm k r Wp Wq} (hT : T ∈ Θ) :
    T.word.length ≤ opOrder Θ := by
  unfold opOrder
  induction Θ with
  | nil => simp at hT
  | cons T' Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hT with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `RealPlaceData.inSS at hp`. Establish `ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r` using `mul_mem_uh (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp.1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp.2.1.1)`. Establish `hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r` using `mul_mem_uh hp.2.2.2.1 hp.2.2.1.1`. Establish `h1` using `ckOn_translate h ha hb`. Use `set L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)) with hL`.

Establish `h2` using `ckOn_clm h1 L`. Establish `heq : rho D p F = fun g => L (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1)))`. Use function extensionality and compare the values at `g`. Simplify using `only [rho, sgs, hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, Matrix.mul_assoc]`. Rewrite using `[heq]`.

Conclude with `h2`.
-/
theorem ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (h : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  unfold RealPlaceData.inSS at hp
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    mul_mem_uh (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp.1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := mul_mem_uh hp.2.2.2.1 hp.2.2.1.1
  have h1 := ckOn_translate h ha hb
  set L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)) with hL
  have h2 := ckOn_clm h1 L
  have heq : rho D p F = fun g => L (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g *
      (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext g
    simp only [rho, sgs, hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, Matrix.mul_assoc]
  rw [heq]
  exact h2

end adj

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D UU Θ _hUU hsm hcom F F' hF hF' _hsF hsF' hIC p hp`. Establish `hf : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (rho D p F)` using `ckOn_rho D hp hF`. Establish `hφ : ∀ T ∈ Θ, CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (fun x => T.coefAdj x (F' x))` using `fun T hT => ckOn_coef (hsm T hT).2 hF' hsF'`. Establish `hleft : Ph D (opApply Θ F) F' p = ∫ g : Mt k r, (Θ.map fun T => hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))).sum ∂D.μG`. Unfold `Ph`.

Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [haar_ae D.haarG] with g hg`. Distinguish the cases in `hgU : (Matrix.of g : Mat k r) ∈ UU`. Rewrite using `[← hcom p hp F (ckOn_mono (by exact_mod_cast Nat.le_add_right _ _) hF) _ hgU]`. Unfold `opApply`.

Rewrite using `[hs_listSum_left]`. Simplify using `only [DTerm.adj_id]`. Establish `h0 : F' (Matrix.of g) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hgU (hsF' (subset_closure ⟨hg, hne⟩))`.

Rewrite using `[h0, hs_zero_right]`. Simplify using `[hs_zero_right]`. Establish `hright : Ph D F (opAdj Θ F') p = ∫ g : Mt k r, (Θ.map fun T => (-1 : ℂ) ^ T.word.length * hsInner (rho D p F (Matrix.of g)) (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))).sum ∂D.μG`. Unfold `Ph`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Unfold `opAdj`. Rewrite using `[hs_listSum_right]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `T _`. Rewrite using `[hs_smul_right]`. Simplify using the standard rewrite rules. Establish `hlen : ∀ T ∈ Θ, T.word.length + 1 ≤ opOrder Θ + 5` using `fun T hT => by`. Use `len_le_order Θ hT` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hIl : ∀ T ∈ Θ, Integrable (fun g : Mt k r => hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))) D.μG`. Introduce `T hT`. Use `hs_integrable D (B := fun x => T.coefAdj x (F' x)) (ckOn_continuousOn (ckOn_Rw hf T.word T.word_lie 0 (by have := hlen T hT; omega))) (ckOn_continuousOn (hφ T hT)) ?_` and prove the remaining obligations. Simplify `hIC p hp T hT 0 0 le_rfl (Nat.zero_le _)` using `[Rw]`.

Establish `hIr : ∀ T ∈ Θ, Integrable (fun g : Mt k r => (-1 : ℂ) ^ T.word.length * hsInner (rho D p F (Matrix.of g)) (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))) D.μG`. Introduce `T hT`. Use `(hs_integrable D (ckOn_continuousOn hf) (ckOn_continuousOn (ckOn_Rw (hφ T hT) T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) 0 (by have := hlen T hT; simp only [List.length_reverse]; omega))) ?_).const_mul _` and prove the remaining obligations. Simplify `hIC p hp T hT T.word.length T.word.length le_rfl le_rfl` using `[Rw]`. Rewrite using `[hleft, hright, (integral_listSum D.μG Θ _ hIl).2, (integral_listSum D.μG Θ _ hIr).2]`.

Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `T hT`. Use `word_adj D T.word T.word_lie (hlen T hT) hf (hφ T hT) (hIC p hp T hT) T.word.length le_rfl` as an intermediate fact. Rewrite using `[this, integral_const_mul]`.

Simplify using `[Rw]`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.phase_function_adjoint : Formalism.FourierDecayAlt.B.StepPhAdj := by
  intro k r Wp Wq _ _ _ _ _ _ D UU Θ _hUU hsm hcom F F' hF hF' _hsF hsF' hIC p hp
  have hf : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (rho D p F) := ckOn_rho D hp hF
  have hφ : ∀ T ∈ Θ, CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) (fun x => T.coefAdj x (F' x)) :=
    fun T hT => ckOn_coef (hsm T hT).2 hF' hsF'
  have hleft : Ph D (opApply Θ F) F' p = ∫ g : Mt k r, (Θ.map fun T =>
      hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))).sum ∂D.μG := by
    unfold Ph
    apply integral_congr_ae
    filter_upwards [haar_ae D.haarG] with g hg
    by_cases hgU : (Matrix.of g : Mat k r) ∈ UU
    · rw [← hcom p hp F (ckOn_mono (by exact_mod_cast Nat.le_add_right _ _) hF) _ hgU]
      unfold opApply
      rw [hs_listSum_left]
      simp only [DTerm.adj_id]
    · have h0 : F' (Matrix.of g) = 0 := by
        by_contra hne
        exact hgU (hsF' (subset_closure ⟨hg, hne⟩))
      rw [h0, hs_zero_right]
      simp [hs_zero_right]
  have hright : Ph D F (opAdj Θ F') p = ∫ g : Mt k r, (Θ.map fun T => (-1 : ℂ) ^ T.word.length *
      hsInner (rho D p F (Matrix.of g))
        (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))).sum ∂D.μG := by
    unfold Ph
    congr 1
    funext g
    unfold opAdj
    rw [hs_listSum_right]
    congr 1
    apply List.map_congr_left
    intro T _
    rw [hs_smul_right]
    simp
  have hlen : ∀ T ∈ Θ, T.word.length + 1 ≤ opOrder Θ + 5 := fun T hT => by
    have := len_le_order Θ hT; omega
  have hIl : ∀ T ∈ Θ, Integrable (fun g : Mt k r =>
      hsInner (Rw T.word (rho D p F) (Matrix.of g)) (T.coefAdj (Matrix.of g) (F' (Matrix.of g)))) D.μG := by
    intro T hT
    refine hs_integrable D (B := fun x => T.coefAdj x (F' x))
      (ckOn_continuousOn (ckOn_Rw hf T.word T.word_lie 0 (by have := hlen T hT; omega)))
      (ckOn_continuousOn (hφ T hT)) ?_
    simpa [Rw] using hIC p hp T hT 0 0 le_rfl (Nat.zero_le _)
  have hIr : ∀ T ∈ Θ, Integrable (fun g : Mt k r => (-1 : ℂ) ^ T.word.length *
      hsInner (rho D p F (Matrix.of g))
        (Rw T.word.reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g))) D.μG := by
    intro T hT
    refine (hs_integrable D (ckOn_continuousOn hf)
      (ckOn_continuousOn (ckOn_Rw (hφ T hT) T.word.reverse
        (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) 0
        (by have := hlen T hT; simp only [List.length_reverse]; omega))) ?_).const_mul _
    simpa [Rw] using hIC p hp T hT T.word.length T.word.length le_rfl le_rfl
  rw [hleft, hright, (integral_listSum D.μG Θ _ hIl).2, (integral_listSum D.μG Θ _ hIr).2]
  congr 1
  apply List.map_congr_left
  intro T hT
  have := word_adj D T.word T.word_lie (hlen T hT) hf (hφ T hT) (hIC p hp T hT) T.word.length le_rfl
  rw [this, integral_const_mul]
  simp [Rw]

end Formalism.FourierDecayAlt.P.B5
