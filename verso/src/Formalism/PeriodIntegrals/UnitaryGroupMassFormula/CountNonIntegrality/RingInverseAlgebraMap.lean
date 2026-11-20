import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Use `first`. Consider the case `exact (NumberField.IsCMField.complexConj_eq_self_iff _).mpr t.2`. Consider the case `exact (NumberField.IsCMField.complexConj_eq_self_iff (K := D.host.E) (t : D.host.E)).mpr t.2`. Consider the case `exact NumberField.IsCMField.complexConj_apply_of_mem_maximalRealSubfield t.2`.

Consider the case `exact NumberField.IsCMField.complexConj_apply_eq_self_of_mem t.2`. Consider the case `exact (NumberField.IsCMField.star_eq_self_iff _).mpr t.2`. Consider the case `exact (NumberField.IsCMField.mem_maximalRealSubfield_iff_star_eq _).mp t.2`. Consider the case `exact (NumberField.IsCMField.complexConj D.host.E).commutes t`.
-/
theorem star_coeF (D : Formalism.BasicNotions.D7) (t : D.host.F) : star (t : D.host.E) = t := by
  haveI := D.host.isCMField_hostE
  first
  | exact (NumberField.IsCMField.complexConj_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.complexConj_eq_self_iff (K := D.host.E) (t : D.host.E)).mpr t.2
  | exact NumberField.IsCMField.complexConj_apply_of_mem_maximalRealSubfield t.2
  | exact NumberField.IsCMField.complexConj_apply_eq_self_of_mem t.2
  | exact (NumberField.IsCMField.star_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.mem_maximalRealSubfield_iff_star_eq _).mp t.2
  | exact (NumberField.IsCMField.complexConj D.host.E).commutes t

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Use `first`. Consider the case `exact ringChar.Nat.cast_ringChar`. Consider the case `(unfold Loc.resChar; exact ringChar.Nat.cast_ringChar)`.
-/
theorem resChar_mem' (D : Formalism.BasicNotions.D7) (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  first
  | exact ringChar.Nat.cast_ringChar
  | (unfold Loc.resChar; exact ringChar.Nat.cast_ringChar)

/- English proof (translation)
Establish `hmem` using `resChar_mem' D p`. Establish `h1 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) = (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F)` using `(map_natCast _ _).symm`. Rewrite using `[h1]`. Establish `hv : p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) < 1`. Use `(p.valuation_lt_one_iff_mem (K := D.host.F) ((Loc.resChar p : ℕ) : 𝓞 D.host.F)).mpr hmem` as an intermediate fact.

Simplify using `using this`. Establish `hnot : ¬ ((D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F))`. Rewrite using `[(D.s.atP p).val, map_one]`. Conclude with `not_le.mpr hv`. Rewrite `hnot` using `[map_one]`.

Rewrite using `[← not_le, ← map_one (valuation (D.s.atP p).Fp)]`. Use `first`. Consider the case `exact fun h => hnot ((Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)`. Consider the case `exact fun h => hnot ((Valuation.Compatible.rel_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)`. Consider the case `exact fun h => hnot (ValuativeRel.valuation_le_valuation.mp h)`.

Consider the case `exact fun h => hnot ((ValuativeRel.valuation_le_valuation_iff _ _).mp h)`. Consider the case `simpa using hnot`. Consider the case `simpa [ValuativeRel.valuation_le_valuation] using hnot`.
-/
theorem val_resChar_lt (D : Formalism.BasicNotions.D7) (p : PlF D) :
    valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp)) < 1 := by
  have hmem := resChar_mem' D p
  have h1 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) =
      (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F) := (map_natCast _ _).symm
  rw [h1]
  have hv : p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) < 1 := by
    have := (p.valuation_lt_one_iff_mem (K := D.host.F) ((Loc.resChar p : ℕ) : 𝓞 D.host.F)).mpr hmem
    simpa using this
  have hnot : ¬ ((D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F)) := by
    rw [(D.s.atP p).val, map_one]
    exact not_le.mpr hv
  rw [map_one] at hnot
  rw [← not_le, ← map_one (valuation (D.s.atP p).Fp)]
  first
  | exact fun h => hnot ((Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot ((Valuation.Compatible.rel_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot (ValuativeRel.valuation_le_valuation.mp h)
  | exact fun h => hnot ((ValuativeRel.valuation_le_valuation_iff _ _).mp h)
  | simpa using hnot
  | simpa [ValuativeRel.valuation_le_valuation] using hnot

/- English proof (translation)
Introduce `D δ M hag p`. Use `haveI := (D.s.atP p).lf`. Use `haveI := (D.s.atP p).ellPrime`. Establish `hδ : δ p ≠ 0` using `(hag p).2.1`. Establish `hz` using `hT D δ M hag p`.

Take `⟨k, hk⟩` from `hS (D.s.atP p).Fp (δ p) ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) (val_resChar_lt D p)`. Take `⟨t, htr, μ, hμ, hι⟩` from `hA D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont (D.s.atP p).qlFin (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val (δ p)⁻¹ hz k`. Use `⟨t, htr, ?_⟩` and prove the remaining obligations. Establish `he : δ p * (D.s.atP p).ιF t = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ`. Rewrite using `[hι, mul_add, mul_inv_cancel₀ hδ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hμ' : valuation (D.s.atP p).Fp μ ≤ 1` using `(Valuation.mem_integer_iff _ _).mp hμ`. Establish `hwv : valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hμ') hk`.

Establish `h1 : valuation (D.s.atP p).Fp (1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) = 1`. Rewrite using `[Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]`. Rewrite using `[he]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Establish `h2` using `congrArg (valuation (D.s.atP p).Fp) h0`. Rewrite `h2` using `[h1, map_zero]`. Conclude with `one_ne_zero h2`. Conclude with `(Valuation.mem_integer_iff _ _).mpr (le_of_eq h1)`. Conclude with `(Valuation.mem_integer_iff _ _).mpr (by rw [map_inv₀, h1, inv_one])`.
-/
theorem locDiff_of (hT : TrDual) (hA : DualApprox) (hS : PowSmall) : LocDiff := by
  intro D δ M hag p
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).ellPrime
  have hδ : δ p ≠ 0 := (hag p).2.1
  have hz := hT D δ M hag p
  obtain ⟨k, hk⟩ := hS (D.s.atP p).Fp (δ p) ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) (val_resChar_lt D p)
  obtain ⟨t, htr, μ, hμ, hι⟩ := hA D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont (D.s.atP p).qlFin
    (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val (δ p)⁻¹ hz k
  refine ⟨t, htr, ?_⟩
  have he : δ p * (D.s.atP p).ιF t =
      1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ := by
    rw [hι, mul_add, mul_inv_cancel₀ hδ]
    ring
  have hμ' : valuation (D.s.atP p).Fp μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
  have hwv : valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hμ') hk
  have h1 : valuation (D.s.atP p).Fp (1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h2 := congrArg (valuation (D.s.atP p).Fp) h0
    rw [h1, map_zero] at h2
    exact one_ne_zero h2
  · exact (Valuation.mem_integer_iff _ _).mpr (le_of_eq h1)
  · exact (Valuation.mem_integer_iff _ _).mpr (by rw [map_inv₀, h1, inv_one])

/- English proof (translation)
Establish `h0 : (D.host.g 0 : ℚ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 0).ne_zero`. Establish `h1 : (D.host.g 1 : ℚ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 1).ne_zero`. Unfold `uP gpart Lat.gS`. Use `split_ifs with ha hb`. Use `⟨D.host.g 1, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Use `⟨D.host.g 0, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Use `⟨D.host.g 0 * D.host.g 1, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`.
-/
theorem unitAt_mul_natCast (D : Formalism.BasicNotions.D7) (p : PlF D) : ∃ n : ℕ, (uP p : ℚ) * n = 1 := by
  have h0 : (D.host.g 0 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have h1 : (D.host.g 1 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  unfold uP gpart Lat.gS
  split_ifs with ha hb
  · refine ⟨D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0 * D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)

/- English proof (translation)
Rewrite using `[(D.s.atP p).O_def]`. Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨c, hc⟩` using `rfl`. Rewrite using `[e]`. Conclude with `isIntegral_algebraMap`.
-/
theorem algMap_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨c, hc⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

/- English proof (translation)
Establish `h` using `Ring.inverse_unit (Units.map (algebraMap A B : A →* B) (Units.mk0 y hy))`. Simplify using `using h`.
-/
theorem ringInverse_algebraMap {A B : Type*} [Field A] [CommRing B] [Algebra A B] (y : A) (hy : y ≠ 0) :
    Ring.inverse (algebraMap A B y) = algebraMap A B y⁻¹ := by
  have h := Ring.inverse_unit (Units.map (algebraMap A B : A →* B) (Units.mk0 y hy))
  simpa using h

/- English proof (translation)
Introduce `D δ M hag p m`. Take `⟨t, htr, hu0, -, hinv⟩` from `hD D δ M hag p`. Take `⟨n, hn⟩` from `unitAt_mul_natCast D p`. Establish `hx : ((t : D.host.E) * (n : D.host.E)) ^ m ∈ ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Rewrite using `[mul_pow]`.

Establish `h` using `Submodule.smul_mem ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E).coeToSubmodule ((n : 𝓞 D.host.E) ^ m) (hP D t htr m)`. Rewrite `h` using `[Algebra.smul_def]`. Simplify `h` using `[mul_comm]`. Establish `hstar : star (((t : D.host.E) * (n : D.host.E)) ^ m) = ((t : D.host.E) * (n : D.host.E)) ^ m`. Rewrite using `[star_pow, star_mul', star_coeF D t, star_natCast]`.

Establish `hnE : ((uP p : ℚ) : D.host.E) * (n : D.host.E) = 1`. Establish `h` using `congrArg (fun q : ℚ => (q : D.host.E)) hn`. Simplify using `using h`. Establish `ha : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)` using `by show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) = _`. Rewrite using `[(D.s.atP p).compat t, ← map_mul]`.

Establish `key : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ * ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) = 1`. Establish `e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ * ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s. …` using `by ring`. Rewrite using `[e1, ha, ← map_mul (D.s.atP p).ιE, hnE, map_one, mul_one, ← map_mul, mul_inv_cancel₀ hu0, map_one]`. Establish `alg : ∀ (R : Type) [CommRing R] (a b c d e : R), a * b * c * (d * e) = 1 → (a * b) ^ m * (c ^ m * (d * e) ^ m) = 1`. Introduce `R _ a b c d e h`.

Combine the equalities or inequalities in the displayed calculation. Establish `hprod : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m * ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m * (D.s.atP p).ιE (((t : D.host.E) * (n : D.host.E)) ^ m)) = 1`. Rewrite using `[map_pow, map_mul]`. Conclude with `alg _ _ _ _ _ _ key`. Use `⟨((t : D.host.E) * (n : D.host.E)) ^ m, hx, hstar, (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m, Subring.pow_mem _ (algMap_mem_O D p _ hinv) m, ?_⟩` and prove the remaining obligations.

Conclude with `Ring.inverse_unit ⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩`.
-/
theorem locGen_of (hD : LocDiff) (hP : DualPow) : LocGen := by
  intro D δ M hag p m
  obtain ⟨t, htr, hu0, -, hinv⟩ := hD D δ M hag p
  obtain ⟨n, hn⟩ := unitAt_mul_natCast D p
  have hx : ((t : D.host.E) * (n : D.host.E)) ^ m ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [mul_pow]
    have h := Submodule.smul_mem
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E).coeToSubmodule
      ((n : 𝓞 D.host.E) ^ m) (hP D t htr m)
    rw [Algebra.smul_def] at h
    simpa [mul_comm] using h
  have hstar : star (((t : D.host.E) * (n : D.host.E)) ^ m) = ((t : D.host.E) * (n : D.host.E)) ^ m := by
    rw [star_pow, star_mul', star_coeF D t, star_natCast]
  have hnE : ((uP p : ℚ) : D.host.E) * (n : D.host.E) = 1 := by
    have h := congrArg (fun q : ℚ => (q : D.host.E)) hn
    simpa using h
  have ha : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t) := by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
      (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) = _
    rw [(D.s.atP p).compat t, ← map_mul]
  have key : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
      ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) = 1 := by
    have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) =
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E)) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) := by ring
    rw [e1, ha, ← map_mul (D.s.atP p).ιE, hnE, map_one, mul_one, ← map_mul, mul_inv_cancel₀ hu0, map_one]
  have alg : ∀ (R : Type) [CommRing R] (a b c d e : R), a * b * c * (d * e) = 1 →
      (a * b) ^ m * (c ^ m * (d * e) ^ m) = 1 := by
    intro R _ a b c d e h
    calc (a * b) ^ m * (c ^ m * (d * e) ^ m) = (a * b * c * (d * e)) ^ m := by ring
      _ = 1 := by rw [h, one_pow]
  have hprod : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m *
      ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m *
        (D.s.atP p).ιE (((t : D.host.E) * (n : D.host.E)) ^ m)) = 1 := by
    rw [map_pow, map_mul]
    exact alg _ _ _ _ _ _ key
  refine ⟨((t : D.host.E) * (n : D.host.E)) ^ m, hx, hstar,
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m,
    Subring.pow_mem _ (algMap_mem_O D p _ hinv) m, ?_⟩
  exact Ring.inverse_unit ⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩

end PI.CntNotIntW
