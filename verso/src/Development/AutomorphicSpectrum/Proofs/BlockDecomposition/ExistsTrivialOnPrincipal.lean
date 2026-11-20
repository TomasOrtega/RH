import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.CharTriv

/- English proof (translation)
Establish `step : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Establish `hw` using `h k`. Use `set w := z ^ (2 ^ k) with hwdef`. Establish `e : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1)`. Rewrite using `[hwdef, pow_succ 2 k, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖`. Establish `e2 : (2 : ℂ) = (w + 1) - (w - 1)` using `by ring`. Establish `h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖`. Rewrite using `[e2]`. Conclude with `norm_sub_le _ _`.

Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e, norm_mul, pow_succ]`. Establish `hn : 0 ≤ ‖w - 1‖` using `norm_nonneg _`. Establish `hz : 0 ≤ ‖z - 1‖` using `norm_nonneg _`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hn]`. Assume the negation of the conclusion as `hne`. Establish `pos : 0 < ‖z - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)`. Establish `h1 : 1 < (3 / 2 : ℝ) ^ k * ‖z - 1‖`.

Rewrite `hk` using `[div_lt_iff₀ pos]`. Then use the resulting hypothesis. Use `step k` as an intermediate fact. Use `h k` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_sq_iter_near (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have step : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hw := h k
      set w := z ^ (2 ^ k) with hwdef
      have e : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
        rw [hwdef, pow_succ 2 k, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
        have e2 : (2 : ℂ) = (w + 1) - (w - 1) := by ring
        have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
          rw [e2]; exact norm_sub_le _ _
        have h4 : ‖(2 : ℂ)‖ = 2 := by simp
        linarith
      rw [e, norm_mul, pow_succ]
      have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
      have hz : 0 ≤ ‖z - 1‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2 hn]
  by_contra hne
  have pos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : 1 < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := by
    rwa [div_lt_iff₀ pos] at hk
  have := step k
  have := h k
  linarith

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : a ^ (k + 1) - 1 = (a ^ k - 1) * (a - 1) + (a ^ k - 1) + (a - 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `add_mem (add_mem (valBall_antitone (by omega) (mul_mem_valBall ih ha)) ih) ha`.
-/
theorem pow_sub_one_mem_valBall {n : ℤ} (hn : 0 ≤ n) {a : F} (ha : a - 1 ∈ valBall F n) (k : ℕ) :
    a ^ k - 1 ∈ valBall F n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - 1 = (a ^ k - 1) * (a - 1) + (a ^ k - 1) + (a - 1) := by ring
    rw [e]
    exact add_mem (add_mem (valBall_antitone (by omega) (mul_mem_valBall ih ha)) ih) ha

end GlobalTheory.CompanionTheory.CharTriv

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ν hν n₀`. Establish `hc : Continuous ν` using `hν.1`. Establish `hV : IsOpen {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}` using `isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const`. Establish `hU : ν ⁻¹' {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ)` using `hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simp))`. Rewrite `hU` using `[Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap]`.

Take `⟨t, ht, htU⟩` from `hU`. Establish `hshift : Filter.Tendsto (fun x : F => x + 1) (𝓝 0) (𝓝 ((1 : Fˣ) : F))`. Use `(continuous_add_right (1 : F)).tendsto (0 : F)` as an intermediate fact. Simplify using `using this`. Take `⟨m, -, hm⟩` from `hasBasis_nhds_zero_valBall.mem_iff.1 (hshift ht)`.

Use `⟨max n₀ (max 1 m.toNat), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `hle : m ≤ ((max n₀ (max 1 m.toNat) : ℕ) : ℤ)` using `by omega`. Establish `key : ∀ k : ℕ, ‖((ν a : ℂˣ) : ℂ) ^ (2 ^ k) - 1‖ < 1 / 2`. Introduce `k`.

Establish `h1` using `GlobalTheory.CompanionTheory.CharTriv.pow_sub_one_mem_valBall (Int.natCast_nonneg _) ha (2 ^ k)`. Establish `h2 : ((a ^ (2 ^ k) : Fˣ) : F) ∈ t`. Use `hm (valBall_antitone hle h1)` as an intermediate fact. Simplify using `using this`. Establish `h3` using `htU (show a ^ (2 ^ k) ∈ (Units.val : Fˣ → F) ⁻¹' t from h2)`.

Simplify using `using h3`. Conclude with `Units.ext (by simpa using GlobalTheory.CompanionTheory.CharTriv.eq_one_of_sq_iter_near _ key)`.
-/
theorem GlobalTheory.CompanionTheory.CharTriv.exists_trivial_on_principal : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ν : Fˣ →* ℂˣ), IsUnit1 ν → ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ 1 ≤ n ∧ ∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → ν a = 1 := by
  intro F _ _ _ _ _ _ ν hν n₀
  have hc : Continuous ν := hν.1
  have hV : IsOpen {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
  have hU : ν ⁻¹' {z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simp))
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  have hshift : Filter.Tendsto (fun x : F => x + 1) (𝓝 0) (𝓝 ((1 : Fˣ) : F)) := by
    have := (continuous_add_right (1 : F)).tendsto (0 : F)
    simpa using this
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 (hshift ht)
  refine ⟨max n₀ (max 1 m.toNat), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro a ha
  have hle : m ≤ ((max n₀ (max 1 m.toNat) : ℕ) : ℤ) := by omega
  have key : ∀ k : ℕ, ‖((ν a : ℂˣ) : ℂ) ^ (2 ^ k) - 1‖ < 1 / 2 := by
    intro k
    have h1 := GlobalTheory.CompanionTheory.CharTriv.pow_sub_one_mem_valBall (Int.natCast_nonneg _) ha (2 ^ k)
    have h2 : ((a ^ (2 ^ k) : Fˣ) : F) ∈ t := by
      have := hm (valBall_antitone hle h1)
      simpa using this
    have h3 := htU (show a ^ (2 ^ k) ∈ (Units.val : Fˣ → F) ⁻¹' t from h2)
    simpa using h3
  exact Units.ext (by simpa using GlobalTheory.CompanionTheory.CharTriv.eq_one_of_sq_iter_near _ key)
