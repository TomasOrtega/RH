import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Conv

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E}` using `(Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)`. Use `closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, b, -, rfl⟩` from `mem_orderC.1 hx`. Establish `: algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b)`.

Rewrite using `[map_add]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)`.
-/
theorem mem_integers_of_mem_hatO {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    y v ∈ v.adicCompletionIntegers E := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  refine closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
    rw [map_add]; rfl
  rw [this]
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)

/- English proof (translation)
Take `⟨n, hn, hy⟩` from `PI.AdCpctDenWork.exists_nat_adele (y : Af E)`. Use `⟨n, hn, fun x hx => ?_⟩` and prove the remaining obligations. Use `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_` and prove the remaining obligations. Establish `h1` using `mul_mem (hy v) (mem_integers_of_mem_hatO hx v)`. Establish `h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x)`.

Rewrite using `[map_mul, map_natCast]`. Take the linear combination `((n : Af E) * algebraMap E (Af E) x) * y.mul_inv`. Establish `h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E`. Rewrite using `[← h2]`. Conclude with `h1`.

Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)`.
-/
theorem exists_denominator (c : Ideal (OF E)) (y : (Af E)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ lattice c y, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * x := by
  obtain ⟨n, hn, hy⟩ := PI.AdCpctDenWork.exists_nat_adele (y : Af E)
  refine ⟨n, hn, fun x hx => ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
  have h1 := mul_mem (hy v) (mem_integers_of_mem_hatO hx v)
  have h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x) := by
    rw [map_mul, map_natCast]
    linear_combination ((n : Af E) * algebraMap E (Af E) x) * y.mul_inv
  have h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E := by
    rw [← h2]; exact h1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)

omit [NumberField E] in

/- English proof (translation)
Use `⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩` and prove the remaining obligations. Establish `h : ∃ b', Ideal.span {b'} = Ideal.span {b}` using `⟨b, rfl⟩`. Simplify using `only [dif_pos h]`. Conclude with `Ideal.span_singleton_eq_span_singleton.1 h.choose_spec`.
-/
theorem exists_generator : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by
  classical
  refine ⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩
  have h : ∃ b', Ideal.span {b'} = Ideal.span {b} := ⟨b, rfl⟩
  simp only [dif_pos h]
  exact Ideal.span_singleton_eq_span_singleton.1 h.choose_spec

/- English proof (translation)
Introduce `E _ _ _ c y t _ ht`. Take `⟨n, hn, hL⟩` from `exists_denominator c y`. Use `choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1`. Take `⟨g, hg⟩` from `exists_generator (E := E)`. Use `choose u hu using hg`.

Establish `hn' : (n : E) ≠ 0` using `by exact_mod_cast hn.ne'`. Set `f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E)` to `fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})`. Establish `hf : Function.Injective f`. Introduce `q q' h`. Take `⟨h1, h2⟩` from `Prod.mk.inj h`.

Establish `h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E`. Rewrite using `[← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]`. Take `⟨v, hv⟩` from `(IsCMField.mem_realUnits_iff E _).1 h3`. Establish `h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q`. Rewrite using `[hv]`.

Establish `e1` using `hu (b q)`. Establish `e2` using `hu (b q')`. Rewrite `e2` using `[← h2]`. Rewrite using `[Units.val_mul]`. Take the linear combination `(-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1 - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv`.

Establish `h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out`. Apply `mul_left_cancel₀ hn'` to reduce the goal to its premises. Rewrite using `[← hb q', h4, map_mul, hb q, mul_left_comm]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]`. Conclude with `Quotient.sound ⟨v, h5⟩`. Establish `hI` using `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1`. Establish `hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t)`. Use `(summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩` and prove the remaining obligations.

Conclude with `Summable.of_finite`. Establish `hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)|`. Rewrite using `[abs_pos]`. Conclude with `(Algebra.norm_ne_zero_iff.2 hn')` after adjusting the coercions. Use `((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_` and prove the remaining obligations.

Establish `h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) = |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)|`. Rewrite using `[Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs, ← Algebra.coe_norm_int]`. Simplify using the standard rewrite rules. Use `show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _`. Rewrite using `[h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]`.

Simplify using the standard rewrite rules.
-/
theorem summable_norm_rpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by
  intro E _ _ _ c y t _ ht
  obtain ⟨n, hn, hL⟩ := exists_denominator c y
  choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1
  obtain ⟨g, hg⟩ := exists_generator (E := E)
  choose u hu using hg
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  let f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E) :=
    fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})
  have hf : Function.Injective f := by
    intro q q' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E := by
      rw [← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E _).1 h3
    have h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q := by
      rw [hv]
      have e1 := hu (b q)
      have e2 := hu (b q')
      rw [← h2] at e2
      rw [Units.val_mul]
      linear_combination (-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1
        - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv
    have h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out := by
      apply mul_left_cancel₀ hn'
      rw [← hb q', h4, map_mul, hb q, mul_left_comm]; rfl
    apply Subtype.ext
    rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
    exact Quotient.sound ⟨v, h5⟩
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1
  have hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t) := by
    refine (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩
    exact Summable.of_finite
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hn')
  refine ((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_
  have h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) =
      |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs,
      ← Algebra.coe_norm_int]
    simp
  show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _
  rw [h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]
  simp

end GlobalTheory.CMVal.Conv
