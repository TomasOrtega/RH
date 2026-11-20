import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h2` using `D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD`. Establish `h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Rewrite using `[h2, map_neg, h3]`. Simplify using the standard rewrite rules.
-/
theorem conj_sqrtMinusD : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h2 := D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h2, map_neg, h3]
  simp

/- English proof (translation)
Rewrite using `[← sq]`. Conclude with `D.host.sqd_sq`.
-/
theorem sqrtMinusD_mul_self : D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E) := by
  rw [← sq]
  exact D.host.sqd_sq

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]`.
-/
theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

/- English proof (translation)
The claim follows from `D.host.conjE_mem_hostF_iff x`.
-/
theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x :=
  D.host.conjE_mem_hostF_iff x

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero`.
-/
theorem d_ne_zero : ((D.host.d : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero

/- English proof (translation)
Introduce `h`. Use `sqrtMinusD_mul_self D` as an intermediate fact. Rewrite `this` using `[h, zero_mul, eq_comm, neg_eq_zero]`. Conclude with `d_ne_zero D this`.
-/
theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have := sqrtMinusD_mul_self D
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact d_ne_zero D this

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]`. Introduce `x _`. Use `set c := D.host.conj`. Use `set s := D.host.sqrtMinusD`. Establish `hs : s ≠ 0` using `sqrtMinusD_ne_zero D`.

Establish `hcs : c s = -s` using `conj_sqrtMinusD D`. Establish `hcc : c (c x) = x` using `conj_conj D x`. Establish `hu : (x + c x) / 2 ∈ D.host.F`. Rewrite using `[mem_F_iff]`. Use `show c ((x + c x) / 2) = _`.

Rewrite using `[map_div₀, map_add, hcc, map_ofNat, add_comm]`. Establish `hv : (x - c x) / (2 * s) ∈ D.host.F`. Rewrite using `[mem_F_iff]`. Use `show c ((x - c x) / (2 * s)) = _`. Rewrite using `[map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hK : s ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx]`. Use `add_mem (Subfield.subset_closure (Or.inl hu)) (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))` and prove the remaining obligations.
-/
theorem hypEFK : Formalism.MainNotions.SphericalInertData.HypEFK D := by
  rw [Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]
  intro x _
  set c := D.host.conj
  set s := D.host.sqrtMinusD
  have hs : s ≠ 0 := sqrtMinusD_ne_zero D
  have hcs : c s = -s := conj_sqrtMinusD D
  have hcc : c (c x) = x := conj_conj D x
  have hu : (x + c x) / 2 ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x + c x) / 2) = _
    rw [map_div₀, map_add, hcc, map_ofNat, add_comm]
  have hv : (x - c x) / (2 * s) ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x - c x) / (2 * s)) = _
    rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]
    field_simp
    ring
  have hK : s ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s := by
    field_simp
    ring
  rw [hx]
  refine add_mem (Subfield.subset_closure (Or.inl hu))
    (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))

/- English proof (translation)
Establish `h` using `D.host.finrank_hostF`. Use `show 2 ≤ Module.finrank ℚ (D.host.F)`. Rewrite using `[h]`. Use `D.R.ord_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_finrank : 2 ≤ Module.finrank ℚ D.host.F := by
  have h := D.host.finrank_hostF
  show 2 ≤ Module.finrank ℚ (D.host.F)
  rw [h]
  have := D.R.ord_pos
  omega

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits Polynomial

variable (D : D7)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩`.
-/
theorem d_eq : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by
  have := D.host.hyp.2.2.2.1; omega⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `d_eq D`. Use `⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩` and prove the remaining obligations. Establish `: (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X)` using `by ring`. Rewrite using `[this]`. Use `(monic_X_pow 2).add_of_left ?_` and prove the remaining obligations.

Use `lt_of_le_of_lt (degree_sub_le _ _) ?_` and prove the remaining obligations. Rewrite using `[degree_X_pow, degree_X]`. Use `max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)` and prove the remaining obligations. Establish `hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1`. Establish `: ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E)` using `by rw [hm]`.

Move the coercions through the operations in `at this`. Take the linear combination `this`. Simplify using `only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]`. Simplify using `only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]`. Use `push_cast`.

Rewrite `hy` using `[hd]`. Take the linear combination `(1/4 : D.host.E) * hy`.
-/
theorem isIntegral_half (y : D.host.E) (hy : y * y = -((D.host.d : ℕ) : D.host.E)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨m, hm⟩ := d_eq D
  refine ⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩
  · have : (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X) := by ring
    rw [this]
    refine (monic_X_pow 2).add_of_left ?_
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [degree_X_pow, degree_X]
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)
  · have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [hd] at hy
    linear_combination (1/4 : D.host.E) * hy

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

/- English proof (translation)
Use `set s := D.host.sqrtMinusD`. Establish `hss : s * s = -((D.host.d : ℕ) : D.host.E)` using `sqrtMinusD_mul_self D`. Establish `hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E)` using `by rw [neg_mul_neg]; exact hss`. Establish `hcs : D.host.conj s = -s` using `conj_sqrtMinusD D`. Take `⟨m, hm⟩` from `d_eq D`.

Set `α : 𝓞 D.host.E` to `⟨(1 + s) / 2, isIntegral_half D s hss⟩`. Set `β : 𝓞 D.host.E` to `⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩`. Establish `hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2` using `rfl`. Establish `hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2` using `rfl`. Establish `hsum : α + β = 1`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E)`. Conclude with `(map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)`. Use `show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[key]`.

Establish `hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1`. Establish `: ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E)` using `by rw [hm]`. Move the coercions through the operations in `at this`. Take the linear combination `this`. Rewrite `hss` using `[hd]`.

Take the linear combination `(-1/4 : D.host.E) * hss`. Establish `hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[hα, hβ, map_div₀, map_add, map_one, hcs, map_ofNat]`. Establish `hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[← hcα, conj_conj]`.

Establish `hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal`. Introduce `x y hxy hx hy`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))`. Establish `hmem : α * β ∈ w.asIdeal`. Rewrite using `[hprod]`.

Conclude with `Ideal.mul_mem_right _ _ h2`. Break down `w.isPrime.mem_or_mem hmem with ha | hb` into its components or cases. Use `⟨α, ha, fun y hy => ?_⟩` and prove the remaining obligations. Establish `: y = β` using `RingOfIntegers.coe_injective (hy.trans hcα)`. Rewrite using `[this]`.

Conclude with `hne α β hsum ha`. Use `⟨β, hb, fun y hy => ?_⟩` and prove the remaining obligations. Establish `: y = α` using `RingOfIntegers.coe_injective (hy.trans hcβ)`. Rewrite using `[this]; exact hne β α (by rw [add_comm]; exact hsum) hb`.
-/
theorem isSplitPl_of_two_mem (w : PlE D.host) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    IsSplitPl D.host w := by
  set s := D.host.sqrtMinusD
  have hss : s * s = -((D.host.d : ℕ) : D.host.E) := sqrtMinusD_mul_self D
  have hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E) := by rw [neg_mul_neg]; exact hss
  have hcs : D.host.conj s = -s := conj_sqrtMinusD D
  obtain ⟨m, hm⟩ := d_eq D
  let α : 𝓞 D.host.E := ⟨(1 + s) / 2, isIntegral_half D s hss⟩
  let β : 𝓞 D.host.E := ⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩
  have hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2 := rfl
  have hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2 := rfl
  have hsum : α + β = 1 := by
    apply RingOfIntegers.ext
    show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)
    push_cast
    ring
  have hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E) := by
      exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)
    show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)
    rw [key]
    have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    rw [hd] at hss
    linear_combination (-1/4 : D.host.E) * hss
  have hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E) := by
    rw [hα, hβ, map_div₀, map_add, map_one, hcs, map_ofNat]
  have hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E) := by
    rw [← hcα, conj_conj]
  have hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal := by
    intro x y hxy hx hy
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))
  have hmem : α * β ∈ w.asIdeal := by
    rw [hprod]; exact Ideal.mul_mem_right _ _ h2
  rcases w.isPrime.mem_or_mem hmem with ha | hb
  · refine ⟨α, ha, fun y hy => ?_⟩
    have : y = β := RingOfIntegers.coe_injective (hy.trans hcα)
    rw [this]; exact hne α β hsum ha
  · refine ⟨β, hb, fun y hy => ?_⟩
    have : y = α := RingOfIntegers.coe_injective (hy.trans hcβ)
    rw [this]; exact hne β α (by rw [add_comm]; exact hsum) hb

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

/- English proof (translation)
Introduce `D hdef`. Use `⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩` and prove the remaining obligations.
-/
theorem jointCond_of_definite : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)) →
    GlobalDatumCompatibility D := by
  intro D hdef
  refine ⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩

end GlobalTheory.DesignBC
