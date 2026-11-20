import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

/- English proof (translation)
Introduce `l _ ϖ hϖ a`. Take `⟨_, _, -, -, hK, -⟩` from `GlobalTheory.AinfChecks.padicComplex l`. Establish `hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ}` using `(hK ϖ hϖ).1`. Use `GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2` and prove the remaining obligations. Introduce `x hx n y hn`.

Establish `hx2 : x ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ}` using `hk ▸ RingHom.mem_ker.2 hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hx2`. Take `⟨c', hc⟩` from `GlobalTheory.RingBasics.exists_pow_div_factorial l n`. Establish `hc' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') = ((l : ℕ) : Per.AinfP l) ^ n`. Establish `h` using `congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc`.

Rewrite `h` using `[map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply]`. Then use the resulting hypothesis. Establish `hX : algebraMap (Per.Ainf l) (Per.AinfP l) (c * (((l : ℕ) : Per.Ainf l) - Per.tm ϖ)) = -algebraMap (Per.Ainf l) (Per.AinfP l) c * (((l : ℕ) : Per.AinfP l) * beta ϖ)`. Rewrite using `[l_mul_beta, map_mul, map_sub, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : y = algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') * (-algebraMap (Per.Ainf l) (Per.AinfP l) c) ^ n * beta ϖ ^ n`.

Apply `(GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hn, hX, mul_pow, mul_pow, ← hc']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _)) (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)`.
-/
theorem acris0_le_sa : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  intro l _ ϖ hϖ a
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  refine GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2
  intro x hx n y hn
  have hx2 : x ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ RingHom.mem_ker.2 hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx2
  obtain ⟨c', hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
  have hc' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') =
      ((l : ℕ) : Per.AinfP l) ^ n := by
    have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
    rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
  have hX : algebraMap (Per.Ainf l) (Per.AinfP l) (c * (((l : ℕ) : Per.Ainf l) - Per.tm ϖ)) =
      -algebraMap (Per.Ainf l) (Per.AinfP l) c * (((l : ℕ) : Per.AinfP l) * beta ϖ) := by
    rw [l_mul_beta, map_mul, map_sub, map_natCast]; ring
  have key : y = algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c') *
      (-algebraMap (Per.Ainf l) (Per.AinfP l) c) ^ n * beta ϖ ^ n := by
    apply (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [hn, hX, mul_pow, mul_pow, ← hc']
    ring
  rw [key]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _))
    (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end GlobalTheory.Pst.StLat
