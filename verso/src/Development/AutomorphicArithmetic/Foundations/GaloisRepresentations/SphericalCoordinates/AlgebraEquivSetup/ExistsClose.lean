import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Establish `hd` using `InfinitePlace.denseRange_algebraMap_pi E`. Take `⟨x, hx⟩` from `hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v)) (by norm_num : (0:ℝ) < 1/2)`. Use `⟨x, fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `(dist_le_pi_dist _ _ v).trans_lt hx`. Rewrite `h1` using `[dist_comm, dist_eq_norm]`.

Conclude with `h1`.
-/
private lemma exists_close {E : Type} [Field E] [NumberField E] (c : InfinitePlace E → E) :
    ∃ x : E, ∀ v : InfinitePlace E, v (x - c v) < 1 / 2 := by
  have hd := InfinitePlace.denseRange_algebraMap_pi E
  obtain ⟨x, hx⟩ := hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v))
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨x, fun v => ?_⟩
  have h1 := (dist_le_pi_dist _ _ v).trans_lt hx
  rw [dist_comm, dist_eq_norm] at h1
  exact h1

/- English proof (translation)
Introduce `E _ _ _ τ₀ M hM`. Take `⟨x, hx⟩` from `exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)`. Establish `hbound : ∀ τ : E →+* ℂ, |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2`. Introduce `τ`. Establish `h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2` using `hx (InfinitePlace.mk τ)`.

Use `lt_of_le_of_lt ?_ h` and prove the remaining obligations. Use `split_ifs with hτ`. Use `Complex.abs_re_le_norm (τ x - -1)` as an intermediate fact. Simplify using `using this`. Use `Complex.abs_re_le_norm (τ x - 1)` as an intermediate fact.

Simplify using `using this`. Establish `hxalg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨y, hy0, hyint⟩` from `IsAlgebraic.exists_integral_multiple hxalg`. Use `set z : E := y • (y • x) with hzdef`. Establish `hz : IsIntegral ℤ z` using `hyint.smul y`.

Establish `hyR : (y : ℝ) ≠ 0` using `by exact_mod_cast hy0`. Establish `hy2 : 0 < (y : ℝ) ^ 2` using `by positivity`. Establish `hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re`. Introduce `τ`. Simplify using `[hzdef, zsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `set w : E := z + IsCMField.complexConj E z with hwdef`. Establish `hw : IsIntegral ℤ w` using `hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)`. Establish `hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re`. Introduce `τ`.

Simplify using `[hwdef, IsCMField.complexEmbedding_complexConj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hneg : (τ₀ w).re < 0`. Establish `hb` using `hbound τ₀`. Rewrite `hb` using `[if_pos rfl]`.

Use `(abs_lt.mp hb).2` as an intermediate fact. Rewrite using `[hτw, hτz]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re`. Introduce `τ hτ`.

Establish `hb` using `hbound τ`. Rewrite `hb` using `[if_neg hτ]`. Use `(abs_lt.mp hb).1` as an intermediate fact. Rewrite using `[hτw, hτz]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hMR : (0 : ℝ) < M` using `by exact_mod_cast hM`. Take `⟨K, hK⟩` from `exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))`. Establish `hKM : 1 < (M : ℝ) * K * -(τ₀ w).re`. Establish `hd : 0 < (M : ℝ) * -(τ₀ w).re` using `by nlinarith`. Rewrite `hK` using `[div_lt_iff₀ hd]`.

Use the polynomial consequences of the given equalities and inequalities. Set `wO : 𝓞 E` to `⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩`. Establish `hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w)`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re`. Introduce `τ`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩` and prove the remaining obligations.

Rewrite using `[hcoe]`. Simplify using `[hwdef, add_comm]`. Rewrite using `[hcoe, hre]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `τ hτ`.

Rewrite using `[hcoe, hre]`. Use `hpos τ hτ` as an intermediate fact. Establish `: 0 ≤ (M : ℝ) * K * (τ w).re` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Gal.W2.Seed.pCEx :
    CEx := by
  intro E _ _ _ τ₀ M hM
  classical
  obtain ⟨x, hx⟩ := exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)
  have hbound : ∀ τ : E →+* ℂ,
      |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2 := by
    intro τ
    have h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2 :=
      hx (InfinitePlace.mk τ)
    refine lt_of_le_of_lt ?_ h
    split_ifs with hτ
    · have := Complex.abs_re_le_norm (τ x - -1)
      simpa using this
    · have := Complex.abs_re_le_norm (τ x - 1)
      simpa using this
  have hxalg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple hxalg
  set z : E := y • (y • x) with hzdef
  have hz : IsIntegral ℤ z := hyint.smul y
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
  have hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re := by
    intro τ
    simp [hzdef, zsmul_eq_mul]
    ring
  set w : E := z + IsCMField.complexConj E z with hwdef
  have hw : IsIntegral ℤ w := hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)
  have hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re := by
    intro τ
    simp [hwdef, IsCMField.complexEmbedding_complexConj]
    ring
  have hneg : (τ₀ w).re < 0 := by
    have hb := hbound τ₀
    rw [if_pos rfl] at hb
    have := (abs_lt.mp hb).2
    rw [hτw, hτz]
    nlinarith
  have hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re := by
    intro τ hτ
    have hb := hbound τ
    rw [if_neg hτ] at hb
    have := (abs_lt.mp hb).1
    rw [hτw, hτz]
    nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))
  have hKM : 1 < (M : ℝ) * K * -(τ₀ w).re := by
    have hd : 0 < (M : ℝ) * -(τ₀ w).re := by nlinarith
    rw [div_lt_iff₀ hd] at hK
    nlinarith
  let wO : 𝓞 E := ⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩
  have hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w) := by
    push_cast
    rfl
  have hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re := by
    intro τ
    simp
    ring
  refine ⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩
  · rw [hcoe]
    simp [hwdef, add_comm]
  · rw [hcoe, hre]
    linarith
  · intro τ hτ
    rw [hcoe, hre]
    have := hpos τ hτ
    have : 0 ≤ (M : ℝ) * K * (τ w).re := by positivity
    linarith
