import Formalism.FlagUnipotentLattices.SubmoduleGeneratorsBound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

open NumberField

/- English proof (translation)
Introduce `E _ _ hc x`. Use `set f := Fintype.card (InfinitePlace E) with hf'`. Establish `hf0 : 0 < f` using `Fintype.card_pos`. Establish `hfR : (0:ℝ) < f` using `by exact_mod_cast hf0`. Establish `hn : finrank ℚ E = 2 * f`.

Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `h2 : InfinitePlace.nrRealPlaces E = 0`. Establish `: IsEmpty {w : InfinitePlace E // w.IsReal}` using `⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1)) w.2⟩`. Conclude with `Fintype.card_eq_zero`. Establish `h3 : InfinitePlace.nrComplexPlaces E = f` using `Fintype.card_congr (Equiv.subtypeUnivEquiv hc)`.

Rewrite `h1` using `[h2, h3]`. Use linear arithmetic over natural numbers and integers. Use `set D : ℝ := |(discr E : ℝ)| with hD`. Establish `hD0 : 0 < D`. Rewrite using `[hD]; exact abs_pos.mpr (by exact_mod_cast discr_ne_zero E)`.

Use `set r : ℝ := D ^ (1 / (finrank ℚ E : ℝ)) with hr`. Establish `hr0 : 0 < r` using `Real.rpow_pos_of_pos hD0 _`. Establish `hr2 : r ^ 2 = D ^ (1 / (f : ℝ))`. Rewrite using `[hr, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, hn]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `set lam : ℝ := 2 * Real.sqrt f / r with hlam`. Establish `hlam0 : 0 < lam` using `by positivity`. Establish `hdim : finrank ℝ (s5bV E) = 2 * f`.

Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ (s5bV E), Complex.finrank_real_complex, finrank_euclideanSpace]`. Take `⟨l, hl, hle⟩` from `hT (s5bV E) (integerEmbeddingLattice hc) lam hlam0 (by`. Introduce `y hy hint`. Establish `hb` using `four_mul_card_le_norm_sq_mul_discr hc y hy hint`. Rewrite `hb` using `[← hf', ← hr2]`.

Establish `h1 : lam ^ 2 ≤ ‖y‖ ^ 2`. Rewrite using `[hlam, div_pow, mul_pow, Real.sq_sqrt hfR.le, div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(pow_le_pow_iff_left₀ hlam0.le (norm_nonneg _) (by norm_num)).mp h1)`. Use the proof step `(WithLp.toLp 2 x)`.

Take `⟨a, rfl⟩` from `(s5bLat_mem hc l).1 hl`. Use `⟨a, fun w => ?_⟩` and prove the remaining obligations. Rewrite `hle` using `[hdim]`. Establish `h1 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ Real.sqrt f * r / 2`. Establish `h2 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ ((2 * f : ℕ) : ℝ) / 2 / lam`.

Rewrite using `[le_div_iff₀ hlam0]`. Conclude with `hle`. Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hlam]`. Use `push_cast`.

Establish `hs : Real.sqrt f * Real.sqrt f = f` using `Real.mul_self_sqrt hfR.le`. Establish `hs0 : 0 < Real.sqrt f` using `Real.sqrt_pos.mpr hfR`. Clear the denominators using the available nonvanishing facts. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : ‖x w - w.embedding (a : E)‖ ≤ ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖` using `PiLp.norm_apply_le ((WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)) w`.

Use `h3.trans (h1.trans (le_of_eq ?_))` and prove the remaining obligations. Establish `h4 : (finrank ℚ E : ℝ) / 2 = f` using `by rw [hn]; push_cast; ring`. Rewrite using `[h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coveringO'_of_transference (hT : Transference) : CoveringO' := by
  intro E _ _ hc x
  classical
  set f := Fintype.card (InfinitePlace E) with hf'
  have hf0 : 0 < f := Fintype.card_pos
  have hfR : (0:ℝ) < f := by exact_mod_cast hf0
  have hn : finrank ℚ E = 2 * f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h2 : InfinitePlace.nrRealPlaces E = 0 := by
      have : IsEmpty {w : InfinitePlace E // w.IsReal} :=
        ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1)) w.2⟩
      exact Fintype.card_eq_zero
    have h3 : InfinitePlace.nrComplexPlaces E = f :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv hc)
    rw [h2, h3] at h1; omega
  set D : ℝ := |(discr E : ℝ)| with hD
  have hD0 : 0 < D := by
    rw [hD]; exact abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  set r : ℝ := D ^ (1 / (finrank ℚ E : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hD0 _
  have hr2 : r ^ 2 = D ^ (1 / (f : ℝ)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, hn]
    congr 1; push_cast; field_simp
  set lam : ℝ := 2 * Real.sqrt f / r with hlam
  have hlam0 : 0 < lam := by positivity
  have hdim : finrank ℝ (s5bV E) = 2 * f := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (s5bV E), Complex.finrank_real_complex, finrank_euclideanSpace]
  obtain ⟨l, hl, hle⟩ := hT (s5bV E) (integerEmbeddingLattice hc) lam hlam0 (by
    intro y hy hint
    have hb := four_mul_card_le_norm_sq_mul_discr hc y hy hint
    rw [← hf', ← hr2] at hb
    have h1 : lam ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hlam, div_pow, mul_pow, Real.sq_sqrt hfR.le, div_le_iff₀ (by positivity)]
      linarith
    exact (pow_le_pow_iff_left₀ hlam0.le (norm_nonneg _) (by norm_num)).mp h1)
    (WithLp.toLp 2 x)
  obtain ⟨a, rfl⟩ := (s5bLat_mem hc l).1 hl
  refine ⟨a, fun w => ?_⟩
  rw [hdim] at hle
  have h1 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ Real.sqrt f * r / 2 := by
    have h2 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ ((2 * f : ℕ) : ℝ) / 2 / lam := by
      rw [le_div_iff₀ hlam0]; exact hle
    refine h2.trans (le_of_eq ?_)
    rw [hlam]; push_cast
    have hs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hfR.le
    have hs0 : 0 < Real.sqrt f := Real.sqrt_pos.mpr hfR
    field_simp
    nlinarith
  have h3 : ‖x w - w.embedding (a : E)‖ ≤ ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ :=
    PiLp.norm_apply_le ((WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)) w
  refine h3.trans (h1.trans (le_of_eq ?_))
  have h4 : (finrank ℚ E : ℝ) / 2 = f := by rw [hn]; push_cast; ring
  rw [h4]; ring

end Formalism.HermitianLatticeCounting.P
