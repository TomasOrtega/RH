import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Establish `hN : (p : F) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Take `⟨h1, h2⟩` from `GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F (p : F) hN`. Establish `he : ∑ σ : F →+* ℂ, Real.log ‖σ (p : F)‖ = (Module.finrank ℚ F : ℝ) * Real.log p`. Simplify using `only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]`. Use `⟨h1.subset fun v hv => by simpa using hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[finsum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_neg_log_adic_abs_eq (F : Type) [Field F] [NumberField F] (p : ℕ) (hp : p.Prime) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (p : F))).Finite ∧
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (p : F)) =
        (Module.finrank ℚ F : ℝ) * Real.log p := by
  have hN : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F (p : F) hN
  have he : ∑ σ : F →+* ℂ, Real.log ‖σ (p : F)‖ = (Module.finrank ℚ F : ℝ) * Real.log p := by
    simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
      nsmul_eq_mul]
  refine ⟨h1.subset fun v hv => by simpa using hv, ?_⟩
  rw [finsum_neg_distrib]
  linarith

/- English proof (translation)
The claim follows from `neg_nonneg.2 (Real.log_nonpos (by positivity) (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v p))`.
-/
theorem neg_log_adicAbv_natCast_nonneg (F : Type) [Field F] [NumberField F] (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (p : F)) :=
  neg_nonneg.2 (Real.log_nonpos (by positivity) (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v p))

/- English proof (translation)
Unfold `htEx`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `h1 : 0 ≤ 1 / ((p : ℝ) - 1)` using `one_div_nonneg.2 (by linarith)`. Check the signs of the components of the expression.
-/
theorem htEx_nonneg' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) : 0 ≤ htEx E p := by
  unfold htEx
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1 : 0 ≤ 1 / ((p : ℝ) - 1) := one_div_nonneg.2 (by linarith)
  positivity

/- English proof (translation)
Introduce `D A κ B`. Use `set S := Pad.setB κ B with hS`. Establish `hpr : ∀ p ∈ S, p.Prime`. Introduce `p hp`. Break down `Finset.mem_union.1 hp with h | h` into its components or cases.

Conclude with `(Finset.mem_filter.1 h).2`. Conclude with `Nat.prime_of_mem_primeFactors h`. Establish `hset : htPrimes κ.l B = (S : Set ℕ)`. Use extensionality with `p`. Establish `hM : κ.l.M' ≠ 0` using `(Nat.lcm_pos (lt_of_lt_of_le (by norm_num) κ.l.three_le) κ.l.A_pos).ne'`.

Establish `hd : 2 * (NumberField.discr D.host.E).natAbs ≠ 0` using `mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))`. Simplify using `only [htPrimes, Set.mem_setOf_eq, hS, Pad.setB, Finset.coe_union, Finset.coe_filter, Set.mem_union, Finset.mem_range, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.lt_succ_iff, ne_eq, mul_ne_zero hd hM, not_false_eq_true, and_true]`. Distinguish the cases in `hp : p.Prime`. Simplify using `only [hp, true_and, and_true, Nat.le_floor_iff' hp.ne_zero]`. Simplify using `only [hp, false_and, and_false, or_self]`.

Establish `hfin : ∀ p ∈ S, (Function.support fun v : HeightOneSpectrum (𝓞 D.what₂.LL) => -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p).Finite` using `fun p hp => (sum_neg_log_adic_abs_eq D.what₂.LL p (hpr p hp)).1.subset (Function.support_mul_subset_left _ _)`. Establish `hterm : ∀ v, ∀ p ∈ S, 0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p` using `fun v p hp => mul_nonneg (neg_log_adicAbv_natCast_nonneg _ p v) (htEx_nonneg' _ p (hpr p hp))`. Use `⟨?_, ?_, fun v => ⟨Finset.sum_nonneg (hterm v), fun p hp => ?_⟩⟩` and prove the remaining obligations. Use `(S.finite_toSet.biUnion fun p hp => hfin p hp).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Simplify using `only [Set.mem_iUnion, Finset.mem_coe, not_exists, Function.mem_support, not_not] at hc`. Conclude with `hv (Finset.sum_eq_zero fun p hp => hc p hp)`. Unfold `htLog htCost`. Rewrite using `[finsum_sum_comm S _ fun p hp => hfin p hp, hset, finsum_mem_coe_finset, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations.

Rewrite using `[← finsum_mul, (sum_neg_log_adic_abs_eq D.what₂.LL p (hpr p hp)).2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hp` using `[hset]`. Conclude with `Finset.single_le_sum (f := fun p : ℕ => -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p) (hterm v) hp`.
-/
theorem htLog_sum : ∀ (D : D7) (A : Amb D) (κ : Lv A) (B : ℝ), (Function.support (htLog κ B)).Finite ∧ ∑ᶠ v, htLog κ B v = (Module.finrank ℚ D.what₂.LL : ℝ) * htCost κ.l B ∧ ∀ v, 0 ≤ htLog κ B v ∧ ∀ p ∈ htPrimes κ.l B, -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p ≤ htLog κ B v := by
  intro D A κ B
  set S := Pad.setB κ B with hS
  have hpr : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact (Finset.mem_filter.1 h).2
    · exact Nat.prime_of_mem_primeFactors h
  have hset : htPrimes κ.l B = (S : Set ℕ) := by
    ext p
    have hM : κ.l.M' ≠ 0 := (Nat.lcm_pos (lt_of_lt_of_le (by norm_num) κ.l.three_le) κ.l.A_pos).ne'
    have hd : 2 * (NumberField.discr D.host.E).natAbs ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
    simp only [htPrimes, Set.mem_setOf_eq, hS, Pad.setB, Finset.coe_union, Finset.coe_filter, Set.mem_union,
      Finset.mem_range, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.lt_succ_iff, ne_eq,
      mul_ne_zero hd hM, not_false_eq_true, and_true]
    by_cases hp : p.Prime
    · simp only [hp, true_and, and_true, Nat.le_floor_iff' hp.ne_zero]
    · simp only [hp, false_and, and_false, or_self]
  have hfin : ∀ p ∈ S, (Function.support fun v : HeightOneSpectrum (𝓞 D.what₂.LL) =>
      -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p).Finite :=
    fun p hp => (sum_neg_log_adic_abs_eq D.what₂.LL p (hpr p hp)).1.subset (Function.support_mul_subset_left _ _)
  have hterm : ∀ v, ∀ p ∈ S,
      0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p :=
    fun v p hp => mul_nonneg (neg_log_adicAbv_natCast_nonneg _ p v) (htEx_nonneg' _ p (hpr p hp))
  refine ⟨?_, ?_, fun v => ⟨Finset.sum_nonneg (hterm v), fun p hp => ?_⟩⟩
  · refine (S.finite_toSet.biUnion fun p hp => hfin p hp).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_iUnion, Finset.mem_coe, not_exists, Function.mem_support, not_not] at hc
    exact hv (Finset.sum_eq_zero fun p hp => hc p hp)
  · unfold htLog htCost
    rw [finsum_sum_comm S _ fun p hp => hfin p hp, hset, finsum_mem_coe_finset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← finsum_mul, (sum_neg_log_adic_abs_eq D.what₂.LL p (hpr p hp)).2]
    ring
  · rw [hset] at hp
    exact Finset.single_le_sum (f := fun p : ℕ =>
      -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p)
      (hterm v) hp

end GlobalTheory.CovHt.Link
