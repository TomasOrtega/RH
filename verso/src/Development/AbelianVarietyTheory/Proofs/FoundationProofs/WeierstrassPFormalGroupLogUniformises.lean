import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

/- English proof (translation)
Establish `hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1`. Use extensionality with `i j`. Conclude with `h1`. Take `⟨v, hv, h, h'⟩` from `(GlobalTheory.FormalInv.exists_substInv_iff (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)`. Conclude with `⟨v (), hv (), h (), h' ()⟩`.
-/
theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

/- English proof (translation)
Use `set l : PowerSeries K := X * m with hl`. Establish `h0 : constantCoeff l = 0` using `by simp [hl]`. Establish `h1 : coeff 1 l = 1`. Rewrite using `[hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]`. Simplify using `using hm`.

Take `⟨ex, he0, he1, he2⟩` from `exists_subst_inverse l h0 h1`. Establish `sl : HasSubst l` using `HasSubst.of_constantCoeff_zero' h0`. Establish `se : HasSubst ex` using `HasSubst.of_constantCoeff_zero' he0`. Establish `hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f`. Introduce `f`.

Rewrite using `[subst_comp_subst_apply se sl, he2]`. Conclude with `congrFun MvPowerSeries.subst_self f`. Establish `hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f`. Introduce `f`. Rewrite using `[subst_comp_subst_apply sl se, he1]`.

Conclude with `congrFun MvPowerSeries.subst_self f`. Use `set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ`. Establish `hQl : (subst l Q : PowerSeries K) = m ^ 2 * q` using `hle _`. Establish `hw : derivative K l = m + X * derivative K m`. Rewrite using `[hl, Derivation.leibniz]`.

Simplify using `[add_comm]`. Establish `hw0 : derivative K l ≠ 0`. Introduce `h`. Use `congrArg constantCoeff (hw.symm.trans h)` as an intermediate fact. Simplify using `[hm] at this`.

Establish `hch` using `derivative_subst (f := Q) sl`. Rewrite `hch` using `[hQl, Derivation.leibniz, Derivation.leibniz_pow]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul] at hch`. Establish `key : l * (subst l (derivative K Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M`. Apply `mul_right_cancel₀ hw0` to reduce the goal to its premises.

Establish `hch' : m ^ 2 * derivative K q + q * (2 * (m * derivative K m)) = (subst l (derivative K Q) : PowerSeries K) * derivative K l` using `by simpa using hch`. Take the linear combination `-l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw + (m ^ 2 * derivative K q + q * (2 * (m * derivative K m))) * hl`. Establish `hQW : IsWpSer a b Q`. Prove the components needed by the constructor for the conclusion. Establish `h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f`.

Introduce `f`. Establish `hf` using `eq_X_mul_shift_add_const f`. Use `conv_lhs => rw [hf]`. Rewrite using `[← coe_substAlgHom se, map_add, map_mul, substAlgHom_X, map_add, map_mul, he0, C_eq_algebraMap, AlgHom.commutes]`. Simplify using the standard rewrite rules.

Rewrite using `[hQ, h2]`. Simplify using `[hm, hq]`. Rewrite using `[← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]`. Use `congr 1`. Establish `hD : derivativeFun Q = derivative K Q` using `rfl`.

Rewrite using `[hD, ← coe_substAlgHom sl]`. Simplify using `only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap, AlgHom.commutes]`. Rewrite using `[coe_substAlgHom sl, hQl]`. Simplify using `only [C_eq_algebraMap] at hM`. Express the relevant statement in the definitionally equal form `(l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ - algebraMap K (PowerSeries K) b * l ^ 6`.

Rewrite using `[key, hl]`. Take the linear combination `m ^ 6 * hM`. Rewrite using `[(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]`.
-/
theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * derivative K q - 2 * q = derivative K (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : derivative K l = m + X * derivative K m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : derivative K l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (derivative K Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * derivative K q + q * (2 * (m * derivative K m)) =
        (subst l (derivative K Q) : PowerSeries K) * derivative K l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * derivative K q + q * (2 * (m * derivative K m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add, map_mul, substAlgHom_X, map_add, map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      have hD : derivativeFun Q = derivative K Q := rfl
      rw [hD, ← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

/- English proof (translation)
Use extensionality with `n`. Simplify using `[dX, coeff_derivative, mul_comm]`.
-/
theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = derivative K f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

/- English proof (translation)
Use extensionality with `n`. Establish `: ((n : ℂ_[p]) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Simplify using `[flog, coeff_derivative, this]`.
-/
theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : derivative ℂ_[p] (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

/- English proof (translation)
Introduce `p _ W wq P hwq hP`. Establish `hw1` using `GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq`. Take `⟨m, hm⟩` from `X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)`. Establish `hm1 : constantCoeff m = 1`. Use `GlobalTheory.GenusOneDatum.coeff_one_flog hwq` as an intermediate fact.

Rewrite `this` using `[hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]`. Simplify using `using this`. Establish `he : wq * wq⁻¹ = 1` using `PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)`. Establish `he1 : constantCoeff wq⁻¹ = 1` using `by simp [PowerSeries.constantCoeff_inv, hw1]`. Use `set e := wq⁻¹ with hedef`.

Use `set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN`. Establish `h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2` using `map_ofNat _ 2`. Establish `hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative ℂ_[p] wq`. Establish `hu : (wq * N)⁻¹ * (wq * N) = 1` using `PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])`. Establish `: omegaW W wq = (-2 * wq - X * derivative ℂ_[p] wq) * (wq * N)⁻¹`.

Rewrite using `[← dX_eq_derivative]`. Both sides reduce to the same expression. Rewrite using `[this, mul_assoc, hu, mul_one]`. Establish `hde : wq * derivative ℂ_[p] e + e * derivative ℂ_[p] wq = 0`. Use `congrArg (derivative ℂ_[p]) he` as an intermediate fact.

Rewrite `this` using `[Derivation.leibniz]`. Simplify using `using this`. Use `set r := W.b₂ / 12 with hr`. Establish `hq : lineSer e (-r) = e + C r * X ^ 2` using `by simp [lineSer]`. Establish `hdq : derivative ℂ_[p] (e + C r * X ^ 2) = derivative ℂ_[p] e + C r * (2 * X)`.

Rewrite using `[map_add, Derivation.leibniz, Derivation.leibniz_pow]`. Simplify using the standard rewrite rules. Establish `hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 + C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3` using `hwq`. Establish `hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e + C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6`. Take the linear combination `e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) + C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he`.

Establish `hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e`. Rewrite using `[hN]`. Take the linear combination `C W.a₃ * X ^ 3 * he`. Establish `c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂`. Establish `: 12 * r = W.a₁ ^ 2 + 4 * W.a₂` using `by rw [hr, WeierstrassCurve.b₂]; ring`.

Simplify `congrArg (C (R := ℂ_[p])) this` using `only [map_mul, map_add, map_pow, map_ofNat]`. Establish `c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) = 12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃)`. Establish `: W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃)`. Rewrite using `[hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Simplify using `only [map_mul, map_add, map_sub, map_pow, map_ofNat]`. Establish `c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) = 2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆)`. Establish `: W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆)`. Rewrite using `[hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using `only [map_mul, map_add, map_sub, map_pow, map_ofNat]`. Establish `main` using `subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1 (by simp [he1]) (by`. Rewrite using `[← hm, derivative_flog, hdq]`.

Take the linear combination `-e ^ 2 * hω + X * e * hde + (omegaW W wq * N * e + 2 * e - X * derivative ℂ_[p] e) * he)`. Use the proof step `(by`. Rewrite using `[hNe, c4, c6]`. Take the linear combination `4 * hW' - X ^ 2 * e ^ 2 * c2)`. Rewrite using `[hq, hm, main]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative ℂ_[p] wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative ℂ_[p] wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative ℂ_[p] e + e * derivative ℂ_[p] wq = 0 := by
    have := congrArg (derivative ℂ_[p]) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : derivative ℂ_[p] (e + C r * X ^ 2) = derivative ℂ_[p] e + C r * (2 * X) := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add, map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * derivative ℂ_[p] e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
