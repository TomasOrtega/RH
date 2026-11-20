import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.OneUnitRoot

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

/- English proof (translation)
Establish `hc` using `GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v`. Use `set n := normV v - 1 with hn`. Establish `hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v` using `Formalism.UG.P.tjcosets_card_residue v`. Use `haveI : Finite (ResidueField (v.adicCompletionIntegers E)) := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v`. Use `haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))`.

Establish `hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0`. Rewrite using `[← hcard, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.cast_card_eq_zero _`. Establish `hq1 : 2 ≤ normV v`. Rewrite using `[← hcard]`.

Conclude with `Finite.one_lt_card`. Establish `hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1`. Rewrite using `[hn, Nat.cast_sub (by omega), hq0]; simp`. Establish `hnpos : 0 < n` using `by omega`. Establish `hy1 : Valued.v (y : v.adicCompletion E) = 1`.

Establish `e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right]`. Conclude with `map_one _`. Rewrite using `[map_one]` and apply the resulting hypothesis. Use `set y' : v.adicCompletionIntegers E := ⟨y, by show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩`.

Establish `hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic` using `monic_X_pow_sub_C y' hnpos.ne'`. Establish `hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E)`. Simplify using `only [eval_sub, eval_pow, eval_X, one_pow, eval_C]`. Rewrite using `[← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Conclude with `ne_of_lt hy`.

Establish `hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X])))`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]`. Rewrite using `[← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]`. Conclude with `isUnit_one.neg`. Take `⟨r, hr, hr1⟩` from `HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E)) _ hm 1 hev (hder.map _)`.

Establish `hrn : r ^ n = y'`. Use `hr` as an intermediate fact. Simplify using `only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this`. Conclude with `sub_eq_zero.1 this`. Establish `hrv : Valued.v (r : v.adicCompletion E) = 1`.

Establish `h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1`. Use `hr1` as an intermediate fact. Rewrite `this` using `[mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Conclude with `lt_of_le_of_ne (r - 1).2 this`. Establish `e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1` using `by ring`.

Rewrite using `[e, Valuation.map_add_eq_of_lt_right]`. Conclude with `map_one _`. Rewrite using `[map_one]` and apply the resulting hypothesis. Establish `hr0 : (r : v.adicCompletion E) ≠ 0`. Introduce `h`.

Rewrite `hrv` using `[h, map_zero]`. Conclude with `zero_ne_one hrv`. Use `⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_mk0]`. Conclude with `congrArg Subtype.val hrn`.
-/
theorem exists_unit_pow_normV_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (y : (v.adicCompletion E)ˣ) (hy : Valued.v ((y : v.adicCompletion E) - 1) < 1) :
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  have hc := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set n := normV v - 1 with hn
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v :=
    Formalism.UG.P.tjcosets_card_residue v
  haveI : Finite (ResidueField (v.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))
  have hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  have hq1 : 2 ≤ normV v := by
    rw [← hcard]; exact Finite.one_lt_card
  have hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1 := by
    rw [hn, Nat.cast_sub (by omega), hq0]; simp
  have hnpos : 0 < n := by omega

  have hy1 : Valued.v (y : v.adicCompletion E) = 1 := by
    have e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  set y' : v.adicCompletionIntegers E := ⟨y, by
    show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩
  have hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic := monic_X_pow_sub_C y' hnpos.ne'
  have hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E) := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ne_of_lt hy
  have hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]
    exact isUnit_one.neg
  obtain ⟨r, hr, hr1⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E))
    _ hm 1 hev (hder.map _)
  have hrn : r ^ n = y' := by
    have := hr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hrv : Valued.v (r : v.adicCompletion E) = 1 := by
    have h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1 := by
      have := hr1
      rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one] at this
      exact lt_of_le_of_ne (r - 1).2 this
    have e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  have hr0 : (r : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hrv; exact zero_ne_one hrv
  refine ⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact congrArg Subtype.val hrn

end GlobalTheory.OneUnitRoot
