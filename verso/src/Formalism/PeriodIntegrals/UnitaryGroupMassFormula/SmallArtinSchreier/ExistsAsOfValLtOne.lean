import Mathlib
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.CoordPowEqZero

namespace PI.UnitaryGroupMassFormula.ASSmall

open scoped NNReal

section Gen

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  (hv : v.Integers O) {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]

include hv in
/- English proof (translation)
Distinguish the cases in `h0 : PreTilt.coeff 0 e = 0`. Conclude with `⟨1, by rw [pow_one, h0]⟩`. Establish `hval : PreTilt.val K v O hv p e = ModP.preVal K v O p (PreTilt.coeff 0 e)`. Express the relevant statement in the definitionally equal form `PreTilt.valAux K v O p e = _`. Rewrite using `[PreTilt.valAux_eq hv h0, pow_zero, pow_one]`.

Take `⟨E, hE⟩` from `Ideal.Quotient.mk_surjective (PreTilt.coeff 0 e)`. Establish `hE0 : (Ideal.Quotient.mk (Ideal.span {(p : O)}) E : ModP O p) ≠ 0`. Rewrite using `[hE]`. Conclude with `h0`. Establish `hvE : v (algebraMap O K E) < 1`.

Rewrite using `[← ModP.preVal_mk hv hE0, hE, ← hval]`. Conclude with `he`. Take `⟨N, hN⟩` from `NNReal.exists_pow_lt_of_lt_one hp hvE`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `hEN : (Ideal.Quotient.mk (Ideal.span {(p : O)}) (E ^ N) : ModP O p) = 0`.

Assume the negation of the conclusion as `h`. Establish `h1` using `(ModP.v_p_lt_val hv).2 h`. Rewrite `h1` using `[map_pow, v.map_pow]`. Conclude with `lt_asymm h1 hN`. Rewrite using `[← hE, ← map_pow]`.

Conclude with `hEN`.
-/
theorem coeff_zero_nilpotent (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ N : ℕ, PreTilt.coeff 0 e ^ N = 0 := by
  by_cases h0 : PreTilt.coeff 0 e = 0
  · exact ⟨1, by rw [pow_one, h0]⟩
  have hval : PreTilt.val K v O hv p e = ModP.preVal K v O p (PreTilt.coeff 0 e) := by
    change PreTilt.valAux K v O p e = _
    rw [PreTilt.valAux_eq hv h0, pow_zero, pow_one]
  obtain ⟨E, hE⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff 0 e)
  have hE0 : (Ideal.Quotient.mk (Ideal.span {(p : O)}) E : ModP O p) ≠ 0 := by
    rw [hE]; exact h0
  have hvE : v (algebraMap O K E) < 1 := by
    rw [← ModP.preVal_mk hv hE0, hE, ← hval]; exact he
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hp hvE
  refine ⟨N, ?_⟩
  have hEN : (Ideal.Quotient.mk (Ideal.span {(p : O)}) (E ^ N) : ModP O p) = 0 := by
    by_contra h
    have h1 := (ModP.v_p_lt_val hv).2 h
    rw [map_pow, v.map_pow] at h1
    exact lt_asymm h1 hN
  rw [← hE, ← map_pow]; exact hEN

include hv in
/- English proof (translation)
Take `⟨N, hN⟩` from `coeff_zero_nilpotent hv hp e he`. Conclude with `⟨solPerf (R := ModP O p) (p := p) e hN, solPerf_spec (R := ModP O p) (p := p) e hN⟩`.
-/
theorem exists_as_of_val_lt_one (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ w : PreTilt O p, w ^ p - w = e := by
  obtain ⟨N, hN⟩ := coeff_zero_nilpotent hv hp e he
  exact ⟨solPerf (R := ModP O p) (p := p) e hN, solPerf_spec (R := ModP O p) (p := p) e hN⟩

end Gen

/- English proof (translation)
Introduce `l _ e he`. Establish `hp : 0 < (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l)`. Rewrite using `[PadicComplex.valuation_p l]`. Establish `: (0 : ℝ≥0) < (l : ℝ≥0)` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression.

Conclude with `exists_as_of_val_lt_one (PadicComplexInt.integers l) hp e he`.
-/
theorem tiltSmall : PI.ArtSch.TiltSmall := by
  intro l _ e he
  have hp : 0 < (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) := by
    rw [PadicComplex.valuation_p l]
    have : (0 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  exact exists_as_of_val_lt_one (PadicComplexInt.integers l) hp e he

end PI.UnitaryGroupMassFormula.ASSmall
