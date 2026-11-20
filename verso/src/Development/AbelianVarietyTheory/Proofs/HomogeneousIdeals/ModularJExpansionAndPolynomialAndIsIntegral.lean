import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion

open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real

noncomputable section

namespace GlobalTheory

local notation "𝕢" => Function.Periodic.qParam

def integralSeries : Subring ℂ⟦X⟧ where
  carrier := {ψ | ∀ k, IsIntegral ℤ (coeff k ψ)}
  mul_mem' {φ ψ} hφ hψ k := by
    rw [coeff_mul]
    exact IsIntegral.sum _ fun x _ ↦ (hφ _).mul (hψ _)
  one_mem' k := by
    rw [coeff_one]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]
  add_mem' {φ ψ} hφ hψ k := by simpa using (hφ k).add (hψ k)
  zero_mem' k := by simpa using isIntegral_zero
  neg_mem' {φ} hφ k := by simpa using (hφ k).neg

/- English proof (translation)
The claim follows from `fun k ↦ by rw [coeff_C] split_ifs exacts [hc, isIntegral_zero]`.
-/
lemma C_mem_integralSeries {c : ℂ} (hc : IsIntegral ℤ c) : C c ∈ integralSeries := fun k ↦ by
  rw [coeff_C]
  split_ifs
  exacts [hc, isIntegral_zero]

/- English proof (translation)
The claim follows from `fun k ↦ by rw [coeff_X] split_ifs exacts [isIntegral_one, isIntegral_zero]`.
-/
lemma X_mem_integralSeries : X ∈ integralSeries := fun k ↦ by
  rw [coeff_X]
  split_ifs
  exacts [isIntegral_one, isIntegral_zero]

def HasUnitLeadingExpansion (n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ (e : ℕ) (ψ : ℂ⟦X⟧), ψ ∈ integralSeries ∧ constantCoeff ψ ≠ 0 ∧
    IsIntegral ℤ (constantCoeff ψ)⁻¹ ∧ HasQExpansion n (fun τ ↦ 𝕢 n τ ^ e * f τ) ψ

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, one_mem _, by simp, by simpa using isIntegral_one, by simpa using HasQExpansion.const n 1⟩`.
-/
lemma HasUnitLeadingExpansion.one (n : ℝ) : HasUnitLeadingExpansion n 1 :=
  ⟨0, 1, one_mem _, by simp, by simpa using isIntegral_one,
    by simpa using HasQExpansion.const n 1⟩

/- English proof (translation)
Take `⟨e, φ, h1, h2, h3, h4⟩` from `hf`. Take `⟨e', ψ, h1', h2', h3', h4'⟩` from `hg`. Use `⟨e + e', φ * ψ, mul_mem h1 h1', by simp [h2, h2'], ?_, (h4.mul h4').congr fun τ ↦ by simp only [Pi.mul_apply]; ring⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_inv]`. Conclude with `h3.mul h3'`.
-/
lemma HasUnitLeadingExpansion.mul {n : ℝ} {f g : ℍ → ℂ} (hf : HasUnitLeadingExpansion n f)
    (hg : HasUnitLeadingExpansion n g) : HasUnitLeadingExpansion n (f * g) := by
  obtain ⟨e, φ, h1, h2, h3, h4⟩ := hf
  obtain ⟨e', ψ, h1', h2', h3', h4'⟩ := hg
  refine ⟨e + e', φ * ψ, mul_mem h1 h1', by simp [h2, h2'], ?_,
    (h4.mul h4').congr fun τ ↦ by simp only [Pi.mul_apply]; ring⟩
  rw [map_mul, mul_inv]
  exact h3.mul h3'

/- English proof (translation)
Establish `: (n : ℂ) ≠ 0` using `by exact_mod_cast hn`. Simplify using `only [Periodic.qParam, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma qParam_one_eq_pow {n : ℕ} (hn : n ≠ 0) (z : ℂ) : 𝕢 1 z = 𝕢 n z ^ n := by
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Take `⟨e, ψ, h1, h2, h3, h4⟩` from `hf`. Establish `hn' : (0 : ℝ) < n` using `by positivity`. Establish `hq (τ : ℍ) : 𝕢 1 τ ≠ 0` using `Periodic.qParam_ne_zero _`. Establish `h5 : HasQExpansion n (fun τ ↦ 𝕢 1 τ ^ e * f τ ^ n) (ψ ^ n)` using `(h4.pow n).congr fun τ ↦ by rw [qParam_one_eq_pow hn]; ring`. Establish `hhol : MDiff fun τ ↦ f τ ^ n`.

Use `(h5.mdifferentiable hn').div (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow e) (fun τ ↦ pow_ne_zero _ (hq τ))` as an intermediate fact. Use `convert! this using 1`. Use extensionality with `τ`. Simplify using `only [Pi.div_apply, Pi.pow_apply]`. Clear denominators, using `[hq τ]` for the nonvanishing conditions.

Establish `hinv' (γ : SL(2, ℤ)) (τ : ℍ) : f (γ • τ) ^ n = f τ ^ n` using `by rw [hinv]`. Establish `h6` using `hasQExpansion_qParam_pow_mul (f := fun τ ↦ f τ ^ n) hinv' hhol (h5.isBoundedAtImInfty hn')`. Use `set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ e * f τ ^ n`. Establish `h7` using `(HasQExpansion.of_hasSum_pow (h := n) (c := fun m ↦ coeff m φ) hn (fun τ ↦ by rw [← qParam_one_eq_pow hn]; exact h6 τ)).unique hn' h5`. Establish `h8 (k : ℕ) : coeff k φ = coeff (n * k) (ψ ^ n)`.

Simplify using `[← h7, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]`. Take `⟨P, hP1, hP2, hP3, hP4⟩` from `exists_polynomial_modularJ_of_hasQExpansion (integralClosure ℤ ℂ).toSubring.toAddSubgroup (f := fun τ ↦ f τ ^ n) hinv' h6 (fun k ↦ h8 k ▸ pow_mem h1 n _)`. Use `set u := constantCoeff ψ ^ n with hu`. Establish `hu0 : u ≠ 0` using `pow_ne_zero _ h2`. Establish `hu1 : IsIntegral ℤ u⁻¹` using `by rw [hu, ← inv_pow]; exact h3.pow n`.

Establish `hP5 : P.coeff e = u` using `by simp [hP2, h8, hu]`. Establish `hP6 : P.leadingCoeff = u`. Rewrite using `[Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hP1 (hP5 ▸ hu0), hP5]`. Establish `hmonic : (Polynomial.C u⁻¹ * P).Monic` using `Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hP6, inv_mul_cancel₀ hu0])`. Establish `heval : (Polynomial.C u⁻¹ * P).eval (modularJ τ₀) = 0`.

Simplify using `[← hP4, h0, hn]`. Use `IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic (fun h ↦ ?_) (heval ▸ isIntegral_zero) fun i ↦ ?_` and prove the remaining obligations. Rewrite `heval` using `[hmonic.natDegree_eq_zero.mp h]`. Simplify using `at heval`. Rewrite using `[Polynomial.coeff_C_mul]`.

Conclude with `hu1.mul (hP3 i)`.
-/
lemma HasUnitLeadingExpansion.isIntegral_modularJ {n : ℕ} (hn : n ≠ 0) {f : ℍ → ℂ}
    (hf : HasUnitLeadingExpansion n f) (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    {τ₀ : ℍ} (h0 : f τ₀ = 0) : IsIntegral ℤ (modularJ τ₀) := by
  obtain ⟨e, ψ, h1, h2, h3, h4⟩ := hf
  have hn' : (0 : ℝ) < n := by positivity
  have hq (τ : ℍ) : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  have h5 : HasQExpansion n (fun τ ↦ 𝕢 1 τ ^ e * f τ ^ n) (ψ ^ n) :=
    (h4.pow n).congr fun τ ↦ by rw [qParam_one_eq_pow hn]; ring
  have hhol : MDiff fun τ ↦ f τ ^ n := by
    have := (h5.mdifferentiable hn').div
      (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow e) (fun τ ↦ pow_ne_zero _ (hq τ))
    convert! this using 1
    ext τ
    simp only [Pi.div_apply, Pi.pow_apply]
    field_simp [hq τ]
  have hinv' (γ : SL(2, ℤ)) (τ : ℍ) : f (γ • τ) ^ n = f τ ^ n := by rw [hinv]
  have h6 := hasQExpansion_qParam_pow_mul (f := fun τ ↦ f τ ^ n) hinv' hhol
    (h5.isBoundedAtImInfty hn')
  set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ e * f τ ^ n
  have h7 := (HasQExpansion.of_hasSum_pow (h := n) (c := fun m ↦ coeff m φ) hn
    (fun τ ↦ by rw [← qParam_one_eq_pow hn]; exact h6 τ)).unique hn' h5
  have h8 (k : ℕ) : coeff k φ = coeff (n * k) (ψ ^ n) := by
    simp [← h7, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  obtain ⟨P, hP1, hP2, hP3, hP4⟩ := exists_polynomial_modularJ_of_hasQExpansion
    (integralClosure ℤ ℂ).toSubring.toAddSubgroup (f := fun τ ↦ f τ ^ n) hinv' h6
    (fun k ↦ h8 k ▸ pow_mem h1 n _)
  set u := constantCoeff ψ ^ n with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ h2
  have hu1 : IsIntegral ℤ u⁻¹ := by rw [hu, ← inv_pow]; exact h3.pow n
  have hP5 : P.coeff e = u := by simp [hP2, h8, hu]
  have hP6 : P.leadingCoeff = u := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hP1 (hP5 ▸ hu0), hP5]
  have hmonic : (Polynomial.C u⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hP6, inv_mul_cancel₀ hu0])
  have heval : (Polynomial.C u⁻¹ * P).eval (modularJ τ₀) = 0 := by
    simp [← hP4, h0, hn]
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic (fun h ↦ ?_)
    (heval ▸ isIntegral_zero) fun i ↦ ?_
  · rw [hmonic.natDegree_eq_zero.mp h] at heval
    simp at heval
  · rw [Polynomial.coeff_C_mul]
    exact hu1.mul (hP3 i)

/- English proof (translation)
Take `⟨J, hJ0, hJ⟩` from `exists_hasQExpansion_modularJ`. Use `⟨_, fun k ↦ ?_, ?_, HasQExpansion.of_hasSum_pow (c := fun m ↦ (coeff m J : ℤ) * ζ ^ m) he fun τ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_mk] split_ifs exacts [(isIntegral_algebraMap (R := ℤ)).mul (hζ.pow _), isIntegral_zero]`. Simplify using `[← coeff_zero_eq_constantCoeff_apply, hJ0]`. Use `hJ (w τ)` as an intermediate fact.

Simplify using `only [hw, coeff_map, eq_intCast] at this`. Use `convert! this using 2 with m`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_hasQExpansion_modularJ_comp {n : ℝ} {w : ℍ → ℍ} {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {e : ℕ}
    (he : e ≠ 0) (hw : ∀ τ, 𝕢 1 (w τ) = ζ * 𝕢 n τ ^ e) :
    ∃ ψ ∈ integralSeries, constantCoeff ψ = 1 ∧
      HasQExpansion n (fun τ ↦ ζ * 𝕢 n τ ^ e * modularJ (w τ)) ψ := by
  obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
  refine ⟨_, fun k ↦ ?_, ?_, HasQExpansion.of_hasSum_pow (c := fun m ↦ (coeff m J : ℤ) * ζ ^ m) he
    fun τ ↦ ?_⟩
  · rw [coeff_mk]
    split_ifs
    exacts [(isIntegral_algebraMap (R := ℤ)).mul (hζ.pow _), isIntegral_zero]
  · simp [← coeff_zero_eq_constantCoeff_apply, hJ0]
  · have := hJ (w τ)
    simp only [hw, coeff_map, eq_intCast] at this
    convert! this using 2 with m
    ring

/- English proof (translation)
Establish `ha : a ≠ 0` using `by rintro rfl; simp [← hn] at hn0`. Establish `hd : d ≠ 0` using `by rintro rfl; simp [← hn] at hn0`. Establish `ha' : (a : ℂ) ≠ 0` using `by exact_mod_cast ha`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd`. Use `set ζ : ℂ := cexp (2 * π * Complex.I * b / d) with hζ`.

Establish `hζd : ζ ^ d = 1`. Rewrite using `[hζ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I b]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hζ0 : ζ ≠ 0` using `Complex.exp_ne_zero _`.

Establish `hζ1 : IsIntegral ℤ ζ` using `.of_pow (Nat.pos_of_ne_zero hd) (hζd ▸ isIntegral_one)`. Establish `hζ2 : IsIntegral ℤ ζ⁻¹` using `.of_pow (Nat.pos_of_ne_zero hd) (by rw [inv_pow, hζd, inv_one]; exact isIntegral_one)`. Take `⟨φ, hφ1, hφ2, hφ3⟩` from `exists_hasQExpansion_modularJ_comp (n := n) (w := id) isIntegral_one hn0 (fun τ ↦ by rw [one_mul, id, qParam_one_eq_pow hn0])`. Take `⟨ψ, hψ1, hψ2, hψ3⟩` from `exists_hasQExpansion_modularJ_comp (n := n) (w := w) hζ1 (e := a * a) (mul_ne_zero ha ha) (fun τ ↦ by`. Simplify using `only [hw, hζ, Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add, ← hn]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Establish `hq` using `HasQExpansion.qParam (n : ℝ)`.

Break down `lt_trichotomy (a * a) n with h | h | h` into its components or cases. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_lt h`. Use `⟨n, φ - C ζ⁻¹ * X ^ (k + 1) * ψ, sub_mem hφ1 (mul_mem (mul_mem (C_mem_integralSeries hζ2) (pow_mem X_mem_integralSeries _)) hψ1), by simp [hφ2], by simpa [hφ2] using isIntegral_one, (hφ3.sub (((HasQExpansion.const _ ζ⁻¹).mul (hq.pow (k + 1))).mul hψ3)).congr fun τ ↦ ?_⟩` and prove the remaining obligations. Generalize the expression as in `𝕢 n τ = q`. Rewrite using `[hk, id]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd ⟨a, h.symm⟩ hsq`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_lt h`. Use `⟨a * a, X ^ (k + 1) * φ - C ζ⁻¹ * ψ, sub_mem (mul_mem (pow_mem X_mem_integralSeries _) hφ1) (mul_mem (C_mem_integralSeries hζ2) hψ1), by simp [hψ2, hζ0], by simpa [hψ2] using hζ1.neg, (((hq.pow (k + 1)).mul hφ3).sub ((HasQExpansion.const _ ζ⁻¹).mul hψ3)).congr fun τ ↦ ?_⟩` and prove the remaining obligations.

Generalize the expression as in `𝕢 n τ = q`. Rewrite using `[hk, id]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasUnitLeadingExpansion_sub {n a d : ℕ} {b : ℤ} (hn : a * d = n) (hn0 : n ≠ 0)
    (hsq : ¬ IsSquare n) {w : ℍ → ℍ} (hw : ∀ τ, (w τ : ℂ) = (a * τ + b) / d) :
    HasUnitLeadingExpansion n fun τ ↦ modularJ τ - modularJ (w τ) := by
  have ha : a ≠ 0 := by rintro rfl; simp [← hn] at hn0
  have hd : d ≠ 0 := by rintro rfl; simp [← hn] at hn0
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  set ζ : ℂ := cexp (2 * π * Complex.I * b / d) with hζ
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I b]
    congr 1
    field_simp
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ1 : IsIntegral ℤ ζ := .of_pow (Nat.pos_of_ne_zero hd) (hζd ▸ isIntegral_one)
  have hζ2 : IsIntegral ℤ ζ⁻¹ := .of_pow (Nat.pos_of_ne_zero hd)
    (by rw [inv_pow, hζd, inv_one]; exact isIntegral_one)
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_hasQExpansion_modularJ_comp (n := n) (w := id)
    isIntegral_one hn0 (fun τ ↦ by rw [one_mul, id, qParam_one_eq_pow hn0])
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := exists_hasQExpansion_modularJ_comp (n := n) (w := w)
    hζ1 (e := a * a) (mul_ne_zero ha ha) (fun τ ↦ by
      simp only [hw, hζ, Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add, ← hn]
      congr 1
      push_cast
      field_simp
      ring)
  have hq := HasQExpansion.qParam (n : ℝ)
  rcases lt_trichotomy (a * a) n with h | h | h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨n, φ - C ζ⁻¹ * X ^ (k + 1) * ψ, sub_mem hφ1 (mul_mem (mul_mem (C_mem_integralSeries hζ2)
      (pow_mem X_mem_integralSeries _)) hψ1), by simp [hφ2], by simpa [hφ2] using isIntegral_one,
      (hφ3.sub (((HasQExpansion.const _ ζ⁻¹).mul (hq.pow (k + 1))).mul hψ3)).congr fun τ ↦ ?_⟩
    generalize 𝕢 n τ = q
    rw [hk, id]
    field_simp
    ring
  · exact absurd ⟨a, h.symm⟩ hsq
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨a * a, X ^ (k + 1) * φ - C ζ⁻¹ * ψ, sub_mem (mul_mem
      (pow_mem X_mem_integralSeries _) hφ1) (mul_mem (C_mem_integralSeries hζ2) hψ1),
      by simp [hψ2, hζ0], by simpa [hψ2] using hζ1.neg,
      (((hq.pow (k + 1)).mul hφ3).sub ((HasQExpansion.const _ ζ⁻¹).mul hψ3)).congr fun τ ↦ ?_⟩
    generalize 𝕢 n τ = q
    rw [hk, id]
    field_simp
    ring

def fixedDetToGL {n : ℕ} (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix A.1) (by
    rw [← RingHom.map_det, A.2]; simpa using hn)

/- English proof (translation)
Rewrite using `[coe_smul_of_det_pos]`. Simplify using `[num, denom, fixedDetToGL]`. Express the relevant statement in the definitionally equal form `0 < ((Int.castRingHom ℝ).mapMatrix A.1).det`. Rewrite using `[← RingHom.map_det, A.2]`. Simplify using `using Nat.pos_of_ne_zero hn`.
-/
lemma coe_fixedDetToGL_smul {n : ℕ} (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) (τ : ℍ) :
    ((fixedDetToGL hn A • τ : ℍ) : ℂ) = (A.1 0 0 * τ + A.1 0 1) / (A.1 1 0 * τ + A.1 1 1) := by
  rw [coe_smul_of_det_pos]
  · simp [num, denom, fixedDetToGL]
  · change 0 < ((Int.castRingHom ℝ).mapMatrix A.1).det
    rw [← RingHom.map_det, A.2]
    simpa using Nat.pos_of_ne_zero hn

/- English proof (translation)
Establish `: fixedDetToGL hn (γ • A) = (γ : GL (Fin 2) ℝ) * fixedDetToGL hn A`. Use extensionality with `i j`. Simplify using `[fixedDetToGL, FixedDetMatrices.smul_coe, Matrix.mul_apply]`. Rewrite using `[this, mul_smul]`. Both sides reduce to the same expression.
-/
lemma fixedDetToGL_smul_smul {n : ℕ} (hn : n ≠ 0) (γ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n)
    (τ : ℍ) : fixedDetToGL hn (γ • A) • τ = γ • fixedDetToGL hn A • τ := by
  have : fixedDetToGL hn (γ • A) = (γ : GL (Fin 2) ℝ) * fixedDetToGL hn A := by
    ext i j
    simp [fixedDetToGL, FixedDetMatrices.smul_coe, Matrix.mul_apply]
  rw [this, mul_smul]
  rfl

/- English proof (translation)
Use `⟨⟨A.1 * γ, by simp [A.2]⟩, fun τ ↦ ?_⟩` and prove the remaining obligations. Establish `: fixedDetToGL hn ⟨A.1 * γ, by simp [A.2]⟩ = fixedDetToGL hn A * (γ : GL (Fin 2) ℝ)`. Use extensionality with `i j`. Simplify using `[fixedDetToGL, Matrix.mul_apply]`. Rewrite using `[this, mul_smul]`.

Both sides reduce to the same expression.
-/
lemma exists_fixedDetToGL_smul_eq {n : ℕ} (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) : ∃ B : FixedDetMatrix (Fin 2) ℤ n,
    ∀ τ : ℍ, fixedDetToGL hn B • τ = fixedDetToGL hn A • γ • τ := by
  refine ⟨⟨A.1 * γ, by simp [A.2]⟩, fun τ ↦ ?_⟩
  have : fixedDetToGL hn ⟨A.1 * γ, by simp [A.2]⟩ = fixedDetToGL hn A * (γ : GL (Fin 2) ℝ) := by
    ext i j
    simp [fixedDetToGL, Matrix.mul_apply]
  rw [this, mul_smul]
  rfl

/- English proof (translation)
Establish `hn : n ≠ 0` using `by rintro rfl; exact hsq IsSquare.zero`. Set `F : FixedDetMatrix (Fin 2) ℤ n → ℍ → ℂ` to `fun A τ ↦ modularJ (fixedDetToGL hn A • τ)`. Establish `hrep (A : FixedDetMatrix (Fin 2) ℤ n) : ∃ B ∈ FixedDetMatrices.reps n, F B = F A`. Establish `hs (γ : SL(2, ℤ)) (B : FixedDetMatrix (Fin 2) ℤ n) : F (γ • B) = F B`. Use extensionality with `τ`.

Simplify using `only [F, fixedDetToGL_smul_smul, modularJ_smul]`. Proceed by induction on `A using FixedDetMatrices.induction_on (m := n) (by exact_mod_cast hn) with`. Consider the case `h0 A h1 h2 h3 h4 => exact ⟨A, ⟨h1, h2, h3, h4⟩, rfl⟩`. Consider the case `hS B hB => rwa [hs]`. Consider the case `hT B hB => rwa [hs]`.

Establish `hfin : (Set.range F).Finite` using `((Set.toFinite (FixedDetMatrices.reps (n : ℤ))).image F).subset <| by`. Introduce and unpack `_ ⟨A, rfl⟩`. Conclude with `hrep A`. Set `Φ : ℍ → ℂ` to `∏ G ∈ hfin.toFinset, fun τ ↦ modularJ τ - G τ`. Establish `hΦ : HasUnitLeadingExpansion n Φ`.

Use `Finset.prod_induction _ _ (fun _ _ ↦ .mul) (.one _) fun G hG ↦ ?_` and prove the remaining obligations. Take `⟨A, rfl⟩` from `hfin.mem_toFinset.mp hG`. Take `⟨B, ⟨h1, h2, -, -⟩, hB⟩` from `hrep A`. Rewrite using `[← hB]`. Establish `hdet : B.1 0 0 * B.1 1 1 = n` using `by simpa [Matrix.det_fin_two, h1] using B.2`.

Establish `h3 : 0 < B.1 1 1`. Establish `: 0 < B.1 0 0 * B.1 1 1` using `by rw [hdet]; positivity`. Conclude with `(pos_iff_pos_of_mul_pos this).mp h2`. Take `⟨a, ha⟩` from `Int.eq_ofNat_of_zero_le h2.le`. Take `⟨d, hd⟩` from `Int.eq_ofNat_of_zero_le h3.le`.

Use `hasUnitLeadingExpansion_sub (a := a) (d := d) (b := B.1 0 1) ?_ hn hsq fun τ ↦ ?_` and prove the remaining obligations. Rewrite `hdet` using `[ha, hd]`. Conclude with `hdet` after adjusting the coercions. Simplify using `[coe_fixedDetToGL_smul, h1, ha, hd]`. Establish `hmem (γ : SL(2, ℤ)) (G : ℍ → ℂ) (hG : G ∈ hfin.toFinset) : (fun τ ↦ G (γ • τ)) ∈ hfin.toFinset`.

Take `⟨A, rfl⟩` from `hfin.mem_toFinset.mp hG`. Take `⟨B, hB⟩` from `exists_fixedDetToGL_smul_eq hn γ A`. Conclude with `hfin.mem_toFinset.mpr ⟨B, funext fun τ ↦ by simp only [F, hB]⟩`. Use `hΦ.isIntegral_modularJ hn (fun γ τ ↦ ?_) ?_` and prove the remaining obligations. Simplify using `only [Φ, Finset.prod_apply, modularJ_smul]`.

Conclude with `Finset.prod_nbij' (fun G τ ↦ G (γ • τ)) (fun G τ ↦ G (γ⁻¹ • τ)) (hmem γ) (hmem γ⁻¹) (fun G _ ↦ by simp only [smul_inv_smul]) (fun G _ ↦ by simp only [inv_smul_smul]) fun _ _ ↦ rfl`. Simplify using `only [Φ, Finset.prod_apply]`. Use `Finset.prod_eq_zero (hfin.mem_toFinset.mpr ⟨M, rfl⟩) ?_` and prove the remaining obligations. Establish `: fixedDetToGL hn M • τ₀ = τ₀`. Use `ext`.

Establish `h` using `denom_ne_zero (fixedDetToGL hn M) τ₀`. Rewrite using `[coe_fixedDetToGL_smul, hM, mul_div_cancel_left₀]`. Simplify `h` using `[denom, fixedDetToGL]`. Simplify using `only [F, this, sub_self]`.
-/
theorem isIntegral_modularJ_of_fixed {n : ℕ} (hsq : ¬ IsSquare n)
    (M : FixedDetMatrix (Fin 2) ℤ n) {τ₀ : ℍ}
    (hM : M.1 0 0 * (τ₀ : ℂ) + M.1 0 1 = (M.1 1 0 * τ₀ + M.1 1 1) * τ₀) :
    IsIntegral ℤ (modularJ τ₀) := by
  classical
  have hn : n ≠ 0 := by rintro rfl; exact hsq IsSquare.zero
  let F : FixedDetMatrix (Fin 2) ℤ n → ℍ → ℂ := fun A τ ↦ modularJ (fixedDetToGL hn A • τ)
  have hrep (A : FixedDetMatrix (Fin 2) ℤ n) : ∃ B ∈ FixedDetMatrices.reps n, F B = F A := by
    have hs (γ : SL(2, ℤ)) (B : FixedDetMatrix (Fin 2) ℤ n) : F (γ • B) = F B := by
      ext τ
      simp only [F, fixedDetToGL_smul_smul, modularJ_smul]
    induction A using FixedDetMatrices.induction_on (m := n) (by exact_mod_cast hn) with
    | h0 A h1 h2 h3 h4 => exact ⟨A, ⟨h1, h2, h3, h4⟩, rfl⟩
    | hS B hB => rwa [hs]
    | hT B hB => rwa [hs]
  have hfin : (Set.range F).Finite :=
    ((Set.toFinite (FixedDetMatrices.reps (n : ℤ))).image F).subset <| by
      rintro _ ⟨A, rfl⟩
      exact hrep A
  let Φ : ℍ → ℂ := ∏ G ∈ hfin.toFinset, fun τ ↦ modularJ τ - G τ
  have hΦ : HasUnitLeadingExpansion n Φ := by
    refine Finset.prod_induction _ _ (fun _ _ ↦ .mul) (.one _) fun G hG ↦ ?_
    obtain ⟨A, rfl⟩ := hfin.mem_toFinset.mp hG
    obtain ⟨B, ⟨h1, h2, -, -⟩, hB⟩ := hrep A
    rw [← hB]
    have hdet : B.1 0 0 * B.1 1 1 = n := by simpa [Matrix.det_fin_two, h1] using B.2
    have h3 : 0 < B.1 1 1 := by
      have : 0 < B.1 0 0 * B.1 1 1 := by rw [hdet]; positivity
      exact (pos_iff_pos_of_mul_pos this).mp h2
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h2.le
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h3.le
    refine hasUnitLeadingExpansion_sub (a := a) (d := d) (b := B.1 0 1) ?_ hn hsq fun τ ↦ ?_
    · rw [ha, hd] at hdet
      exact_mod_cast hdet
    · simp [coe_fixedDetToGL_smul, h1, ha, hd]
  have hmem (γ : SL(2, ℤ)) (G : ℍ → ℂ) (hG : G ∈ hfin.toFinset) :
      (fun τ ↦ G (γ • τ)) ∈ hfin.toFinset := by
    obtain ⟨A, rfl⟩ := hfin.mem_toFinset.mp hG
    obtain ⟨B, hB⟩ := exists_fixedDetToGL_smul_eq hn γ A
    exact hfin.mem_toFinset.mpr ⟨B, funext fun τ ↦ by simp only [F, hB]⟩
  refine hΦ.isIntegral_modularJ hn (fun γ τ ↦ ?_) ?_
  · simp only [Φ, Finset.prod_apply, modularJ_smul]
    exact Finset.prod_nbij' (fun G τ ↦ G (γ • τ)) (fun G τ ↦ G (γ⁻¹ • τ)) (hmem γ) (hmem γ⁻¹)
      (fun G _ ↦ by simp only [smul_inv_smul]) (fun G _ ↦ by simp only [inv_smul_smul])
      fun _ _ ↦ rfl
  · simp only [Φ, Finset.prod_apply]
    refine Finset.prod_eq_zero (hfin.mem_toFinset.mpr ⟨M, rfl⟩) ?_
    have : fixedDetToGL hn M • τ₀ = τ₀ := by
      ext
      have h := denom_ne_zero (fixedDetToGL hn M) τ₀
      rw [coe_fixedDetToGL_smul, hM, mul_div_cancel_left₀]
      simpa [denom, fixedDetToGL] using h
    simp only [F, this, sub_self]

/- English proof (translation)
Establish `hD : 0 < 4 * a * c - b ^ 2`. Establish `h1` using `congrArg Complex.re h`. Establish `h2` using `congrArg Complex.im h`. Simplify using `[pow_two] at h1 h2`. Establish `hy` using `τ.im_pos`.

Establish `h3 : (b : ℝ) = -2 * a * τ.re`. Apply `mul_right_cancel₀ hy.ne'` to reduce the goal to its premises. Take the linear combination `h2`. Establish `h4 : (4 * a * c - b ^ 2 : ℝ) = (2 * a * τ.im) ^ 2`. Rewrite `h1`, the goal using `[h3]`.

Take the linear combination `4 * a * h1`. Establish `h5 : (a : ℝ) ≠ 0` using `by exact_mod_cast ha`. Establish `: (0 : ℝ) < 4 * a * c - b ^ 2` using `by rw [h4]; positivity`. Conclude with `this` after adjusting the coercions. Use `set D := 4 * a * c - b ^ 2 with hD'`.

Use `set k := D + |b| with hk`. Establish `hm : D ≤ 2 * k - b` using `by have := le_abs_self b; have := abs_nonneg b; omega`. Establish `h4 : 4 * (k ^ 2 - b * k + a * c) = (2 * k - b) ^ 2 + D` using `by rw [hD']; ring`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ k ^ 2 - b * k + a * c by nlinarith)`. Use `isIntegral_modularJ_of_fixed (n := n) ?_ ⟨!![k - b, -c; a, k], by rw [← hn, Matrix.det_fin_two_of]; ring⟩ ?_` and prove the remaining obligations.

Introduce and unpack `⟨r, hr⟩`. Establish `h5 : (2 * r : ℤ) ^ 2 = (2 * k - b) ^ 2 + D`. Rewrite using `[← h4, hn, hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Generalize the expression as in `2 * k - b = m at *`. Establish `h6 : m < 2 * r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Use `push_cast`.

Take the linear combination `-h`.
-/
theorem isIntegral_modularJ_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (h : a * (τ : ℂ) ^ 2 + b * τ + c = 0) : IsIntegral ℤ (modularJ τ) := by
  have hD : 0 < 4 * a * c - b ^ 2 := by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have hy := τ.im_pos
    have h3 : (b : ℝ) = -2 * a * τ.re := by
      apply mul_right_cancel₀ hy.ne'
      linear_combination h2
    have h4 : (4 * a * c - b ^ 2 : ℝ) = (2 * a * τ.im) ^ 2 := by
      rw [h3] at h1 ⊢
      linear_combination 4 * a * h1
    have h5 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have : (0 : ℝ) < 4 * a * c - b ^ 2 := by rw [h4]; positivity
    exact_mod_cast this
  set D := 4 * a * c - b ^ 2 with hD'
  set k := D + |b| with hk
  have hm : D ≤ 2 * k - b := by have := le_abs_self b; have := abs_nonneg b; omega
  have h4 : 4 * (k ^ 2 - b * k + a * c) = (2 * k - b) ^ 2 + D := by rw [hD']; ring
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k ^ 2 - b * k + a * c by nlinarith)
  refine isIntegral_modularJ_of_fixed (n := n) ?_
    ⟨!![k - b, -c; a, k], by rw [← hn, Matrix.det_fin_two_of]; ring⟩ ?_
  · rintro ⟨r, hr⟩
    have h5 : (2 * r : ℤ) ^ 2 = (2 * k - b) ^ 2 + D := by
      rw [← h4, hn, hr]; push_cast; ring
    generalize 2 * k - b = m at *
    have h6 : m < 2 * r := by nlinarith
    nlinarith
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast
    linear_combination -h

/- English proof (translation)
Take `⟨p, q, hpq⟩` from `Submodule.mem_span_pair.mp (h τ (Submodule.subset_span (by simp)))`. Take `⟨r, s, hrs⟩` from `Submodule.mem_span_pair.mp (h 1 (Submodule.subset_span (by simp)))`. Simplify using `only [zsmul_eq_mul, mul_one] at hpq hrs`. Use `isIntegral_modularJ_of_quadratic (a := r) (b := s - p) (c := -q) ?_ ?_` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `hα s (by simpa using hrs.symm)`. Use `push_cast`. Take the linear combination `(τ : ℂ) * hrs - hpq`.
-/
theorem isIntegral_modularJ_of_mul_mem {τ : ℍ} {α : ℂ} (hα : ∀ m : ℤ, α ≠ m)
    (h : ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1}, α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp (h τ (Submodule.subset_span (by simp)))
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp (h 1 (Submodule.subset_span (by simp)))
  simp only [zsmul_eq_mul, mul_one] at hpq hrs
  refine isIntegral_modularJ_of_quadratic (a := r) (b := s - p) (c := -q) ?_ ?_
  · rintro rfl
    exact hα s (by simpa using hrs.symm)
  · push_cast
    linear_combination (τ : ℂ) * hrs - hpq

open NumberField in

/- English proof (translation)
Take `⟨α, hα⟩ : ∃ α : 𝓞 K, ∀ m : ℤ, α ≠ m` from `by by_contra! hc`. Use `finrank_le_one (R := ℤ) (1 : 𝓞 K) fun α ↦ by` as an intermediate fact. Take `⟨m, hm⟩` from `hc α`. Conclude with `⟨m, by simp [hm]⟩`. Rewrite `this` using `[RingOfIntegers.rank, hK]`.

Use linear arithmetic over natural numbers and integers. Use `isIntegral_modularJ_of_mul_mem (fun m hm ↦ hα m ?_) (h α)` and prove the remaining obligations. Use `ext`. Apply `ι.injective` to reduce the goal to its premises. Simplify using `using hm`.
-/
theorem isIntegral_modularJ_of_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (ι : K →+* ℂ) {τ : ℍ}
    (h : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
      ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 K, ∀ m : ℤ, α ≠ m := by
    by_contra! hc
    have := finrank_le_one (R := ℤ) (1 : 𝓞 K) fun α ↦ by
      obtain ⟨m, hm⟩ := hc α
      exact ⟨m, by simp [hm]⟩
    rw [RingOfIntegers.rank, hK] at this
    omega
  refine isIntegral_modularJ_of_mul_mem (fun m hm ↦ hα m ?_) (h α)
  ext
  apply ι.injective
  simpa using hm

def halfOneAddSqrtNeg (d : ℕ) (hd : d ≠ 0) : ℍ :=
  ⟨(1 + √d * Complex.I) / 2, by
    have : (0 : ℝ) < √d := Real.sqrt_pos.mpr (by positivity)
    simpa using this⟩

/- English proof (translation)
Use `isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num) ?_` and prove the remaining obligations. Establish `h1 : ((√d : ℝ) : ℂ) ^ 2 = d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp`. Express the relevant statement in the definitionally equal form `_ * ((1 + √d * Complex.I) / 2 : ℂ) ^ 2 + _ * ((1 + √d * Complex.I) / 2 : ℂ) + _ = 0`. Use `push_cast`.

Take the linear combination `((√d : ℝ) : ℂ) ^ 2 * Complex.I_sq - h1`.
-/
theorem isIntegral_modularJ_halfOneAddSqrtNeg (d : ℕ) (hd : d ≠ 0) :
    IsIntegral ℤ (modularJ (halfOneAddSqrtNeg d hd)) := by
  refine isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num) ?_
  have h1 : ((√d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  change _ * ((1 + √d * Complex.I) / 2 : ℂ) ^ 2 + _ * ((1 + √d * Complex.I) / 2 : ℂ) + _ = 0
  push_cast
  linear_combination ((√d : ℝ) : ℂ) ^ 2 * Complex.I_sq - h1

/- English proof (translation)
The claim follows from `isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num) (by push_cast; linear_combination h)`.
-/
theorem isIntegral_modularJ_of_sq_eq_neg {w : ℍ} {d : ℤ} (h : (2 * (w : ℂ) - 1) ^ 2 = -d) :
    IsIntegral ℤ (modularJ w) :=
  isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num)
    (by push_cast; linear_combination h)

/- English proof (translation)
Take `⟨J, hJ0, hJ⟩` from `exists_hasQExpansion_modularJ`. Take `⟨K, hK⟩ : X ∣ J - 1` from `X_dvd_iff.mpr (by`. Rewrite using `[map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, hJ0, sub_self])`. Establish `h1` using `hJ.sub (HasQExpansion.const 1 1)`. Rewrite `h1` using `[map_one, ← map_one (PowerSeries.map (Int.castRingHom ℂ)), ← map_sub, hK, map_mul, map_X]`.

Establish `h2 : HasQExpansion 1 (fun τ ↦ modularJ τ - (𝕢 1 τ)⁻¹) _` using `.of_qParam_mul (h1.congr fun τ ↦ by`. Rewrite using `[mul_sub, mul_inv_cancel₀ (Periodic.qParam_ne_zero _)])`. Conclude with `⟨fun n ↦ coeff n K, fun τ ↦ by simpa using h2 τ⟩`.
-/
theorem exists_hasSum_modularJ_sub_inv : ∃ c : ℕ → ℤ, ∀ τ : ℍ,
    HasSum (fun n ↦ (c n : ℂ) * 𝕢 1 τ ^ n) (modularJ τ - (𝕢 1 τ)⁻¹) := by
  obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
  obtain ⟨K, hK⟩ : X ∣ J - 1 := X_dvd_iff.mpr (by
    rw [map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, hJ0, sub_self])
  have h1 := hJ.sub (HasQExpansion.const 1 1)
  rw [map_one, ← map_one (PowerSeries.map (Int.castRingHom ℂ)), ← map_sub, hK, map_mul,
    map_X] at h1
  have h2 : HasQExpansion 1 (fun τ ↦ modularJ τ - (𝕢 1 τ)⁻¹) _ :=
    .of_qParam_mul (h1.congr fun τ ↦ by
      rw [mul_sub, mul_inv_cancel₀ (Periodic.qParam_ne_zero _)])
  exact ⟨fun n ↦ coeff n K, fun τ ↦ by simpa using h2 τ⟩

open NumberField in

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_hasSum_modularJ_sub_inv, fun _ _ h1 h2 h3 ↦ let ⟨P, a, _, b⟩ := exists_polynomial_modularJ h1 h2 h3; ⟨P, a, b⟩, fun _ _ ↦ isIntegral_modularJ_of_sq_eq_neg, fun _ _ _ hK ι _ ↦ isIntegral_modularJ_of_ringOfIntegers hK ι⟩`.
-/
theorem modularJ_expansion_and_polynomial_and_isIntegral :
    (∃ c : ℕ → ℤ, ∀ τ : ℍ,
      HasSum (fun n ↦ (c n : ℂ) * 𝕢 1 τ ^ n) (modularJ τ - (𝕢 1 τ)⁻¹)) ∧
    (∀ (m : ℕ) (f : ℍ → ℂ), (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) → MDiff f →
      (IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        (∀ i, P.coeff i ∈ AddSubgroup.closure
          (Set.range fun k ↦ coeff k (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ))) ∧
        ∀ τ, f τ = P.eval (modularJ τ)) ∧
    (∀ (w : ℍ) (d : ℤ), (2 * (w : ℂ) - 1) ^ 2 = -d → IsIntegral ℤ (modularJ w)) ∧
    (∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (τ : ℍ),
      (∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
        ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) → IsIntegral ℤ (modularJ τ)) :=
  ⟨exists_hasSum_modularJ_sub_inv,
    fun _ _ h1 h2 h3 ↦ let ⟨P, a, _, b⟩ := exists_polynomial_modularJ h1 h2 h3; ⟨P, a, b⟩,
    fun _ _ ↦ isIntegral_modularJ_of_sq_eq_neg,
    fun _ _ _ hK ι _ ↦ isIntegral_modularJ_of_ringOfIntegers hK ι⟩

end GlobalTheory
