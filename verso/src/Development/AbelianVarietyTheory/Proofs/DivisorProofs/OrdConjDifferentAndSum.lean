import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

/- English proof (translation)
Introduce `E K _ _ _ _ _ i q w hq hm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hd : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Establish `h1` using `DefectSumCompare.vla_discAt i w`. Establish `h2` using `GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w`.

Establish `h3` using `GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm`. Establish `h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) = padicValNat q (discr E).natAbs * vAdd w (q : K)`. Rewrite using `[← h1, ← h3]`. Conclude with `h2`. Establish `h7` using `congrArg (Int.cast : ℤ → ℝ) h5`.

Simplify using `only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7`. Establish `hE : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Rewrite using `[different_vp]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Establish `hE : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`. Establish `h1` using `DefectSumCompare.log_discr_eq E`. Establish `h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ)`.

Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite `h1` using `[h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]`. Establish `h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p = ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ)`. Introduce `p hp`. Rewrite using `[different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h3, ← Finset.sum_div, h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
