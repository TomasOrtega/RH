import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegralPos
open GlobalTheory.TorsionIntegral

open IsLocalRing in

/- English proof (translation)
Introduce `L W m h2 _ hg2 hg3 hΔ hpos hm`. Establish `hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W` using `fun t a b => integral L W m h2 hg2 hg3 hpos.ne' hm a b`. Use `⟨hI, fun t t' a b a' b' hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hne : L.weierstrassP t ≠ L.weierstrassP t'` using `mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc`.

Rewrite `hc` using `[not_or]`. Take `⟨hs, hp⟩` from `sum_prod L b b' hne`. Set `x1 : W` to `⟨_, hI t a b⟩`. Set `x2 : W` to `⟨_, hI t' a' b'⟩`. Set `x3 : W` to `⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩`.

Set `x4 : W` to `⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩`. Set `g2 : W` to `⟨L.g₂, hg2⟩`. Set `g3 : W` to `⟨L.g₃, hg3⟩`. Set `h : W` to `⟨2⁻¹, h2⟩`. Set `e : W` to `⟨_, hΔ⟩`.

Establish `c2 : ((2 : W) : ℂ) = 2` using `rfl`. Establish `c27 : ((27 : W) : ℂ) = 27` using `rfl`. Establish `e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[x1, x2, x3, x4, g2, g3, h, c2]`.

Take the linear combination `hs`. Establish `e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[x1, x2, x3, x4, g2, g3, h]`. Take the linear combination `hp`.

Establish `e3 : 2 * h = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[h, c2]`. Establish `e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[g2, g3, e, c27, disc L]`. Establish `e5 : residue W (x1 - x2) = 0` using `(residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)`. Establish `f1` using `congrArg (residue W) e1`. Establish `f2` using `congrArg (residue W) e2`. Establish `f3` using `congrArg (residue W) e3`.

Establish `f4` using `congrArg (residue W) e4`. Simplify using `only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5`. Rewrite `e5` using `[sub_eq_zero]`. Rewrite `f1`, `f2` using `[← e5]`. Generalize the expression as in `residue W x1 = x at *`.

Generalize the expression as in `residue W g2 = A at *`. Generalize the expression as in `residue W g3 = B at *`. Generalize the expression as in `residue W h = u at *`. Establish `k1 : 4 * x ^ 3 - A * x - B = 0` using `by linear_combination (A * x) * f3 - f1`. Establish `k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0`.

Establish `hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A`. Take the linear combination `A * (2 * u + 1) * f3`. Rewrite using `[← hA]`. Take the linear combination `-16 * f2`. Establish `k3 : A ^ 3 - 27 * B ^ 2 = 0`.

Take the linear combination `(A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1`. Rewrite `f4` using `[k3, zero_mul]`. Conclude with `zero_ne_one f4`.
-/
theorem torsion_integral_distinct_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ),
    (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W →
    0 < m → (m : ℂ)⁻¹ ∈ W →
    (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧
    ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice →
      t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits →
      t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  intro L W m h2 _ hg2 hg3 hΔ hpos hm
  have hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W :=
    fun t a b => integral L W m h2 hg2 hg3 hpos.ne' hm a b
  refine ⟨hI, fun t t' a b a' b' hn => ?_⟩
  by_contra hc
  have hne : L.weierstrassP t ≠ L.weierstrassP t' := mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc
  rw [not_or] at hc
  obtain ⟨hs, hp⟩ := sum_prod L b b' hne
  let x1 : W := ⟨_, hI t a b⟩
  let x2 : W := ⟨_, hI t' a' b'⟩
  let x3 : W := ⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩
  let x4 : W := ⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩
  let g2 : W := ⟨L.g₂, hg2⟩
  let g3 : W := ⟨L.g₃, hg3⟩
  let h : W := ⟨2⁻¹, h2⟩
  let e : W := ⟨_, hΔ⟩
  have c2 : ((2 : W) : ℂ) = 2 := rfl
  have c27 : ((27 : W) : ℂ) = 27 := rfl
  have e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3 := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h, c2]
    linear_combination hs
  have e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2) := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h]
    linear_combination hp
  have e3 : 2 * h = 1 := by
    apply Subtype.ext
    simp [h, c2]
  have e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1 := by
    apply Subtype.ext
    simp [g2, g3, e, c27, disc L]
  have e5 : residue W (x1 - x2) = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)
  have f1 := congrArg (residue W) e1
  have f2 := congrArg (residue W) e2
  have f3 := congrArg (residue W) e3
  have f4 := congrArg (residue W) e4
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5
  rw [sub_eq_zero] at e5
  rw [← e5] at f1 f2
  generalize residue W x1 = x at *
  generalize residue W g2 = A at *
  generalize residue W g3 = B at *
  generalize residue W h = u at *
  have k1 : 4 * x ^ 3 - A * x - B = 0 := by linear_combination (A * x) * f3 - f1
  have k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0 := by
    have hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A := by
      linear_combination A * (2 * u + 1) * f3
    rw [← hA]; linear_combination -16 * f2
  have k3 : A ^ 3 - 27 * B ^ 2 = 0 := by
    linear_combination (A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1
  rw [k3, zero_mul] at f4
  exact zero_ne_one f4

end GlobalTheory.TorsionIntegralPos
