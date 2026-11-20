import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real

namespace GlobalTheory.LatticeAreaBound

/- English proof (translation)
Establish `h1` using `tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹`. Establish `h2` using `tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹`. Simplify using `only [eisG, PeriodPair.G, one_div]`. Use `h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)` and prove the remaining obligations. Break down `eq_or_ne w 0 with rfl | hw` into its components or cases.

Simplify using `[Set.indicator, hk]`. Simplify using `[Set.indicator, hw, h]`.
-/
theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ}
    (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹
  have h2 := tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹
  simp only [eisG, PeriodPair.G, one_div]
  refine h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

/- English proof (translation)
Rewrite using `[TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]`. Both sides reduce to the same expression.
-/
theorem discr_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    TaylorLogMetric.discr Λ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]
  rfl

/- English proof (translation)
Establish `hy` using `τ.im_pos`. Establish `hn` using `norm_pos_iff.2 ha`. Establish `hA : 0 < ‖a‖ ^ 2 * τ.im` using `by positivity`. Establish `key : ∀ m n m' n' : ℤ, ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im)` using `fun m n m' n' => by`. Simplify using `[Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[key, abs_of_nonneg (by simpa using hA.le)]`. Simplify using the standard rewrite rules. Introduce and unpack `b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩`.

Take `⟨m, n, rfl⟩` from `(h _).1 h₁`. Take `⟨m', n', rfl⟩` from `(h _).1 h₂`. Rewrite `hb`, the goal using `[key, abs_mul, abs_of_pos hA]`. Establish `h0 : n * m' - m * n' ≠ 0` using `fun e => by simp [e] at hb`. Establish `h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)|`.

Conclude with `Int.one_le_abs h0` after adjusting the coercions. Conclude with `le_mul_of_one_le_left hA.le h1`.
-/
theorem area_eq {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hA : 0 < ‖a‖ ^ 2 * τ.im := by positivity
  have key : ∀ m n m' n' : ℤ,
      ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im
        = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im) := fun m n m' n' => by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩
  · rw [key, abs_of_nonneg (by simpa using hA.le)]
    simp
  · rintro b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h₁
    obtain ⟨m', n', rfl⟩ := (h _).1 h₂
    rw [key, abs_mul, abs_of_pos hA] at hb ⊢
    have h0 : n * m' - m * n' ≠ 0 := fun e => by simp [e] at hb
    have h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_left hA.le h1

/- English proof (translation)
Take `⟨C, hC⟩` from `CuspFormClass.exists_bound CuspForm.discriminant`. Use `⟨C, fun τ => ?_⟩` and prove the remaining obligations. Establish `h` using `hC τ`. Establish `hy` using `τ.im_pos`. Rewrite `h` using `[CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, le_div_iff₀ (by positivity)]`.

Rewrite using `[mul_comm]` and apply the resulting hypothesis.
-/
theorem exists_bound_discriminant :
    ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ 6 * ‖ModularForm.discriminant τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  have hy := τ.im_pos
  rw [CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
  rwa [mul_comm]

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_bound_discriminant`. Use `⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩` and prove the remaining obligations. Introduce and unpack `Λ ⟨w₁, w₂, hi, rfl⟩ hd`. Set `L : PeriodPair` to `⟨w₁, w₂, hi⟩`. Establish `hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice` using `fun z => by`.

Rewrite using `[AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `[L]`. Take `⟨a, τ, ha, h⟩` from `exists_lattice_eq_mul_tau L`. Establish `hy` using `τ.im_pos`. Establish `hn` using `norm_pos_iff.2 ha`.

Rewrite using `[area_eq ha fun x => (hL x).trans (h x)]`. Rewrite `hd` using `[discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h]`. Establish `e` using `congrArg norm hd`. Rewrite `e` using `[norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le], norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)]`. Establish `hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Break down `le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1` into its components or cases. Conclude with `le_max_of_le_left h1`. Conclude with `le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)`.
-/
theorem area_bounded_of_discr_eq_one : ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → 0 < area Λ ∧ area Λ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_discriminant
  refine ⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩
  rintro Λ ⟨w₁, w₂, hi, rfl⟩ hd
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice := fun z => by
    rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  rw [area_eq ha fun x => (hL x).trans (h x)]
  rw [discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h] at hd
  have e := congrArg norm hd
  rw [norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at e
  have hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C := by
    calc (‖a‖ ^ 2 * τ.im) ^ 6 = ‖a‖ ^ 12 * τ.im ^ 6 := by ring
      _ = (2 * π) ^ 12 * (τ.im ^ 6 * ‖ModularForm.discriminant τ‖) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC τ) (by positivity)
  refine ⟨by positivity, ?_⟩
  rcases le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)

end GlobalTheory.LatticeAreaBound
