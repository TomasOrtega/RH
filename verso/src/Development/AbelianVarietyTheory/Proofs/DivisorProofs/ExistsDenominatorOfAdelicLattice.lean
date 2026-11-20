import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.CMVal.LatBound

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_mul (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_add (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z + z') w = z w + z' w := rfl

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le (w.valuation_le_one b))`.
-/
theorem integral_of_int (b : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (algebraMap (𝓞 E) E b)) w ∈ w.adicCompletionIntegers E :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
    ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le (w.valuation_le_one b))

/- English proof (translation)
Use `integral_of_int (E := E) (n : 𝓞 E) w` as an intermediate fact. Simplify using `using this`.
-/
theorem integral_natCast (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ((n : Af E)) w ∈ w.adicCompletionIntegers E := by
  have := integral_of_int (E := E) (n : 𝓞 E) w
  simpa using this

/- English proof (translation)
Take `⟨x, a, ha, h⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z`. Take `⟨m, hm0, hm⟩` from `IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))`. Establish `hint : IsIntegral ℤ ((m.natAbs : E) * x)`. Break down `Int.natAbs_eq m with h1 | h1` into its components or cases. Establish `: ((m.natAbs : E) * x) = m • x`.

Rewrite using `[zsmul_eq_mul, ← Int.cast_natCast, ← h1]`. Rewrite using `[this]`. Conclude with `hm`. Establish `h1' : (m.natAbs : ℤ) = -m` using `by omega`. Establish `: ((m.natAbs : E) * x) = -(m • x)`.

Rewrite using `[zsmul_eq_mul, ← Int.cast_natCast, h1', Int.cast_neg, neg_mul]`. Rewrite using `[this]`. Conclude with `hm.neg`. Use `⟨m.natAbs, Int.natAbs_pos.2 hm0, fun w => ?_⟩` and prove the remaining obligations. Establish `e : (m.natAbs : Af E) * z = algebraMap E (Af E) (algebraMap (𝓞 E) E ⟨_, hint⟩) + (m.natAbs : Af E) * a`.

Rewrite using `[h, one_smul, mul_add]`. Use `congr 1`. Use `show _ = algebraMap E (Af E) ((m.natAbs : E) * x)`. Rewrite using `[map_mul, map_natCast]`. Rewrite using `[e, coord_add, coord_mul]`.

Conclude with `add_mem (integral_of_int _ w) (mul_mem (integral_natCast _ w) (ha w))`.
-/
theorem exists_nat_mul_integral (z : Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((d : Af E) * z) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨m, hm0, hm⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
  have hint : IsIntegral ℤ ((m.natAbs : E) * x) := by
    rcases Int.natAbs_eq m with h1 | h1
    · have : ((m.natAbs : E) * x) = m • x := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, ← h1]
      rw [this]; exact hm
    · have h1' : (m.natAbs : ℤ) = -m := by omega
      have : ((m.natAbs : E) * x) = -(m • x) := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, h1', Int.cast_neg, neg_mul]
      rw [this]; exact hm.neg
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun w => ?_⟩
  have e : (m.natAbs : Af E) * z =
      algebraMap E (Af E) (algebraMap (𝓞 E) E ⟨_, hint⟩) + (m.natAbs : Af E) * a := by
    rw [h, one_smul, mul_add]
    congr 1
    show _ = algebraMap E (Af E) ((m.natAbs : E) * x)
    rw [map_mul, map_natCast]
  rw [e, coord_add, coord_mul]
  exact add_mem (integral_of_int _ w) (mul_mem (integral_natCast _ w) (ha w))

/- English proof (translation)
Take `⟨a, -, ha, hza⟩` from `(GlobalTheory.CMVal.HatPlace.mem_hatO_iff E c hc z).1 hz`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h1 : Valued.v (z w - a w) ≤ 1` using `(hza w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)`. Establish `h2 : z w = (z w - a w) + a w` using `by ring`. Rewrite using `[h2]`.

Conclude with `Valuation.map_add_le _ h1 (ha w)`.
-/
theorem integral_of_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : z ∈ hatO c)
    (w : HeightOneSpectrum (𝓞 E)) : z w ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, -, ha, hza⟩ := (GlobalTheory.CMVal.HatPlace.mem_hatO_iff E c hc z).1 hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : Valued.v (z w - a w) ≤ 1 :=
    (hza w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have h2 : z w = (z w - a w) + a w := by ring
  rw [h2]
  exact Valuation.map_add_le _ h1 (ha w)

/- English proof (translation)
Introduce `E _ _ _ c hc y`. Take `⟨d₁, hd₁, h₁⟩` from `exists_nat_mul_integral (y : Af E)`. Take `⟨d₂, hd₂, h₂⟩` from `exists_nat_mul_integral (↑y⁻¹ : Af E)`. Establish `hN₁ : 0 < Ideal.absNorm c` using `Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Use `⟨Ideal.absNorm c * d₁ * d₂, by positivity, fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_lattice]`. Establish `hY : ∀ w : HeightOneSpectrum (𝓞 E), (algebraMap E (Af E) (algebraMap (𝓞 E) E x) * (d₁ : Af E) * ((d₂ : Af E) * (↑y⁻¹ : Af E))) w ∈ w.adicCompletionIntegers E` using `fun w => by`. Rewrite using `[coord_mul, coord_mul]`. Conclude with `mul_mem (mul_mem (integral_of_int x w) (integral_natCast d₁ w)) (h₂ w)`. Establish `key` using `GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hY`.

Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_natCast, map_natCast, map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hx` using `[mem_lattice]`.

Establish `hz` using `integral_of_mem_hatO hc hx`. Establish `hint : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E ((d₁ : E) * x) ≤ 1` using `fun w => by`. Establish `e : algebraMap E (Af E) ((d₁ : E) * x) = (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * ((d₁ : Af E) * (y : Af E))`. Rewrite using `[map_mul, map_natCast]`. Establish `: (↑y⁻¹ : Af E) * (y : Af E) = 1` using `Units.inv_mul y`.

Take the linear combination `(-(d₁ : Af E) * algebraMap E (Af E) x) * this`. Establish `h3 : (algebraMap E (Af E) ((d₁ : E) * x)) w ∈ w.adicCompletionIntegers E`. Rewrite using `[e, coord_mul]`. Conclude with `mul_mem (hz w) (h₁ w)`. Rewrite `h3` using `[HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `h3`. Take `⟨b, hb⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ hint`. Establish `e2 : ((Ideal.absNorm c * d₁ * d₂ : ℕ) : E) * x = algebraMap (𝓞 E) E (((Ideal.absNorm c * d₂ : ℕ) : 𝓞 E) * b)`. Rewrite using `[map_mul, hb, map_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `RingOfIntegers.isIntegral_coe _`.
-/
theorem lattice_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧
      ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  intro E _ _ _ c hc y
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_integral (y : Af E)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_integral (↑y⁻¹ : Af E)
  have hN₁ : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm c * d₁ * d₂, by positivity, fun x => ?_, fun x hx => ?_⟩
  · rw [mem_lattice]
    have hY : ∀ w : HeightOneSpectrum (𝓞 E),
        (algebraMap E (Af E) (algebraMap (𝓞 E) E x) * (d₁ : Af E) * ((d₂ : Af E) * (↑y⁻¹ : Af E))) w ∈
          w.adicCompletionIntegers E := fun w => by
      rw [coord_mul, coord_mul]
      exact mul_mem (mul_mem (integral_of_int x w) (integral_natCast d₁ w)) (h₂ w)
    have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hY
    convert key using 1
    rw [map_natCast, map_natCast, map_mul, map_natCast]
    push_cast
    ring
  · rw [mem_lattice] at hx
    have hz := integral_of_mem_hatO hc hx
    have hint : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E ((d₁ : E) * x) ≤ 1 := fun w => by
      have e : algebraMap E (Af E) ((d₁ : E) * x) =
          (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * ((d₁ : Af E) * (y : Af E)) := by
        rw [map_mul, map_natCast]
        have : (↑y⁻¹ : Af E) * (y : Af E) = 1 := Units.inv_mul y
        linear_combination (-(d₁ : Af E) * algebraMap E (Af E) x) * this
      have h3 : (algebraMap E (Af E) ((d₁ : E) * x)) w ∈ w.adicCompletionIntegers E := by
        rw [e, coord_mul]; exact mul_mem (hz w) (h₁ w)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h3
      exact h3
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ hint
    have e2 : ((Ideal.absNorm c * d₁ * d₂ : ℕ) : E) * x =
        algebraMap (𝓞 E) E (((Ideal.absNorm c * d₂ : ℕ) : 𝓞 E) * b) := by
      rw [map_mul, hb, map_natCast]; push_cast; ring
    rw [e2]
    exact RingOfIntegers.isIntegral_coe _

end GlobalTheory.CMVal.LatBound
