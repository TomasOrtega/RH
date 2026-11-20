import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace OrdZeroUnit

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ (𝓞 E)`. Rewrite using `[Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod a)), RingHom.map_det]`. Establish `: (Int.castRingHom (ZMod a)).mapMatrix (Algebra.leftMulMatrix b (1 + (a : 𝓞 E) * y)) = 1`. Rewrite using `[map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast, ← map_natCast (algebraMap (ZMod a) (Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (ZMod a))), ZMod.natCast_self, map_zero, zero_mul, add_zero]`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem norm_modEq_one (a : ℕ) (y : 𝓞 E) :
    (((Algebra.norm ℤ (1 + (a : 𝓞 E) * y) : ℤ)) : ZMod a) = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod a)), RingHom.map_det]
  have : (Int.castRingHom (ZMod a)).mapMatrix (Algebra.leftMulMatrix b (1 + (a : 𝓞 E) * y)) = 1 := by
    rw [map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast,
      ← map_natCast (algebraMap (ZMod a) (Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (ZMod a))), ZMod.natCast_self, map_zero, zero_mul, add_zero]
  rw [this, Matrix.det_one]

/- English proof (translation)
Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E z (fun v => (h v).le)`. Take `⟨y', hy'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E z⁻¹ (fun v => by rw [map_inv₀, h v, inv_one])`. Establish `hyy : y * y' = 1`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_mul, hy, hy', mul_inv_cancel₀ hz, map_one]`.

Conclude with `⟨y, ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩, hy⟩`.
-/
theorem isUnit_of_valuation_eq_one (z : E) (hz : z ≠ 0) (h : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E z = 1) :
    ∃ u : 𝓞 E, IsUnit u ∧ algebraMap (𝓞 E) E u = z := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z (fun v => (h v).le)
  obtain ⟨y', hy'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z⁻¹
    (fun v => by rw [map_inv₀, h v, inv_one])
  have hyy : y * y' = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hy, hy', mul_inv_cancel₀ hz, map_one]
  exact ⟨y, ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩, hy⟩

end OrdZeroUnit
end GlobalTheory

namespace GlobalTheory
namespace OrdZeroUnit

/- English proof (translation)
Introduce `E _ _ w x hx0 hx1 hyp`. Assume the negation of the conclusion as `hne`. Establish `hlt : Valued.v x < 1` using `lt_of_le_of_ne hx1 hne`. Establish `hxpos : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx0`. Establish `ht0 : x * x ≠ 0` using `mul_ne_zero hx0 hx0`.

Establish `htx : Valued.v (x * x) < Valued.v x`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hw_eq : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k - x) ≤ Valued.v (x * x) → w.valuation E k = Valued.v x`. Introduce `k hk`.

Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hk htx)`. Establish `hoff : ∀ (a : ℕ), 0 < a → ∀ (k : E), k ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k - 1) / (a : E)) ≤ 1 → v.valuation E k⁻¹ ≤ 1 → v.valuation E k = 1 ∧ v.valuation E (k - 1) ≤ 1`. Introduce `a ha k hk0 v h1 h2`. Establish `hva : v.valuation E (a : E) ≤ 1`.

Rewrite using `[← map_natCast (algebraMap (𝓞 E) E)]`. Conclude with `v.valuation_le_one _`. Establish `ha0 : (a : E) ≠ 0` using `Nat.cast_ne_zero.2 ha.ne'`. Establish `hk1 : v.valuation E (k - 1) ≤ 1`. Establish `: k - 1 = ((k - 1) / a) * a` using `by field_simp`.

Rewrite using `[this, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hk : v.valuation E k ≤ 1`. Establish `: k = (k - 1) + 1` using `by ring`. Rewrite using `[this]`.

Conclude with `(Valuation.map_add _ _ _).trans (max_le hk1 (by rw [map_one]))`. Use `⟨le_antisymm hk ?_, hk1⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨k₀, hk₀off, hk₀w⟩` from `hyp 1 one_pos (x * x) ht0`. Establish `hw0` using `hw_eq _ hk₀w`.

Establish `hk₀0 : (k₀ : E) ≠ 0` using `k₀.ne_zero`. Establish `hoff0 : ∀ v, v ≠ w → v.valuation E (k₀ : E) = 1` using `fun v hv => (hoff 1 one_pos _ hk₀0 v (hk₀off v hv).1 (hk₀off v hv).2).1`. Take `⟨k₀', hk₀'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (k₀ : E) (fun v => by`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Rewrite using `[hw0]`. Conclude with `hx1`. Conclude with `(hoff0 v hv).le)`. Use `set R : ℕ := (Algebra.norm ℤ k₀').natAbs with hR`. Use `set q : ℕ := Ideal.absNorm w.asIdeal with hq`.

Establish `hqmem : (q : 𝓞 E) ∈ w.asIdeal` using `Ideal.absNorm_mem _`. Establish `hqpos : 0 < q` using `Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))`. Use `set a : ℕ := q * (R + 1) + 1 with ha`. Establish `hapos : 0 < a` using `Nat.succ_pos _`. Establish `hanot : (a : 𝓞 E) ∉ w.asIdeal`.

Introduce `h`. Establish `h1 : (1 : 𝓞 E) ∈ w.asIdeal`. Use `w.asIdeal.sub_mem h (w.asIdeal.mul_mem_right (((R + 1 : ℕ)) : 𝓞 E) hqmem)` as an intermediate fact. Rewrite `this` using `[ha]`. Move the coercions through the operations in `at this`.

Simplify using `using this`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Establish `hwa : w.valuation E (a : E) = 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 E) E) a]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hanot`.

Take `⟨k, hkoff, hkw⟩` from `hyp a hapos (x * x) ht0`. Establish `hwk` using `hw_eq _ hkw`. Establish `hk0 : (k : E) ≠ 0` using `k.ne_zero`. Establish `hoffk : ∀ v, v ≠ w → v.valuation E (k : E) = 1 ∧ v.valuation E ((k : E) - 1) ≤ 1` using `fun v hv => hoff a hapos _ hk0 v (hkoff v hv).1 (hkoff v hv).2`. Take `⟨kk, hkk⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (k : E) (fun v => by`.

Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[hwk]`. Conclude with `hx1`. Conclude with `(hoffk v hv).1.le)`.

Take `⟨u, hu, hue⟩` from `isUnit_of_valuation_eq_one ((k : E) / k₀) (div_ne_zero hk0 hk₀0) (fun v => by`. Rewrite using `[map_div₀]`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[hw0, hwk, div_self hxpos]`.

Rewrite using `[(hoffk v hv).1, hoff0 v hv, div_one])`. Establish `hkku : kk = u * k₀'`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_mul, hkk, hue, hk₀', div_mul_cancel₀ _ hk₀0]`. Establish `hNk : (Algebra.norm ℤ kk).natAbs = R`.

Rewrite using `[hkku, map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 (hu.map _), one_mul]`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (((k : E) - 1) / (a : E)) (fun v => by`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[map_div₀, hwa, div_one, ← hkk, ← map_one (algebraMap (𝓞 E) E), ← map_sub]`.

Conclude with `v.valuation_le_one _`. Conclude with `(hkoff v hv).1)`. Establish `hkky : kk = 1 + (a : 𝓞 E) * y`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Establish `ha0 : (a : E) ≠ 0` using `Nat.cast_ne_zero.2 hapos.ne'`.

Rewrite using `[map_add, map_one, map_mul, map_natCast, hy, hkk]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hcong` using `norm_modEq_one a y`. Rewrite `hcong` using `[← hkky]`.

Establish `hdvd : (a : ℤ) ∣ Algebra.norm ℤ kk - 1` using `(ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ a).1 (by rw [hcong, Int.cast_one])`. Establish `hN1 : Algebra.norm ℤ kk = 1`. Take `⟨c, hc⟩` from `hdvd`. Establish `hA : ((R : ℤ) + 2) ≤ (a : ℤ)`. Rewrite using `[ha]`.

Use `push_cast`. Use polynomial arithmetic with `[(Nat.one_le_cast (α := ℤ)).2 hqpos, (Nat.cast_nonneg R : (0 : ℤ) ≤ R)]`. Establish `hR0 : (0 : ℤ) ≤ R` using `Nat.cast_nonneg R`. Apply the tactic sequence `rcases Int.natAbs_eq (Algebra.norm ℤ kk) with h | h <;> rw [hNk] at h <;> rw [h] at hc ⊢`. Break down `lt_trichotomy c 0 with hc0 | hc0 | hc0` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Substitute `hc0` using the available equality. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Break down `lt_trichotomy c 0 with hc0 | hc0 | hc0` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Substitute `hc0` using the available equality. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `hunit : IsUnit kk`.

Rewrite using `[← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton, hN1]`. Both sides reduce to the same expression. Establish `hmem : kk ∈ w.asIdeal`. Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]`. Express the relevant statement in the definitionally equal form `w.valuation E (algebraMap (𝓞 E) E kk) < 1`.

Rewrite using `[hkk, hwk]`. Conclude with `hlt`. Conclude with `w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)`.
-/
theorem valuation_eq_one_of_approx : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E),
    x ≠ 0 → Valued.v x ≤ 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → Valued.v x = 1 := by
  intro E _ _ w x hx0 hx1 hyp
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have hxpos : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have ht0 : x * x ≠ 0 := mul_ne_zero hx0 hx0
  have htx : Valued.v (x * x) < Valued.v x := by
    rw [map_mul]
    calc Valued.v x * Valued.v x < 1 * Valued.v x := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hxpos)
      _ = Valued.v x := one_mul _

  have hw_eq : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k - x) ≤ Valued.v (x * x) →
      w.valuation E k = Valued.v x := by
    intro k hk
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hk htx)

  have hoff : ∀ (a : ℕ), 0 < a → ∀ (k : E), k ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 E),
      v.valuation E ((k - 1) / (a : E)) ≤ 1 → v.valuation E k⁻¹ ≤ 1 →
      v.valuation E k = 1 ∧ v.valuation E (k - 1) ≤ 1 := by
    intro a ha k hk0 v h1 h2
    have hva : v.valuation E (a : E) ≤ 1 := by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact v.valuation_le_one _
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
    have hk1 : v.valuation E (k - 1) ≤ 1 := by
      have : k - 1 = ((k - 1) / a) * a := by field_simp
      rw [this, map_mul]
      calc v.valuation E ((k - 1) / a) * v.valuation E (a : E) ≤ 1 * 1 := mul_le_mul' h1 hva
        _ = 1 := one_mul _
    have hk : v.valuation E k ≤ 1 := by
      have : k = (k - 1) + 1 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le hk1 (by rw [map_one]))
    refine ⟨le_antisymm hk ?_, hk1⟩
    calc 1 = v.valuation E (k * k⁻¹) := by rw [mul_inv_cancel₀ hk0, map_one]
      _ = v.valuation E k * v.valuation E k⁻¹ := map_mul _ _ _
      _ ≤ v.valuation E k * 1 := mul_le_mul' le_rfl h2
      _ = v.valuation E k := mul_one _

  obtain ⟨k₀, hk₀off, hk₀w⟩ := hyp 1 one_pos (x * x) ht0
  have hw0 := hw_eq _ hk₀w
  have hk₀0 : (k₀ : E) ≠ 0 := k₀.ne_zero
  have hoff0 : ∀ v, v ≠ w → v.valuation E (k₀ : E) = 1 := fun v hv =>
    (hoff 1 one_pos _ hk₀0 v (hk₀off v hv).1 (hk₀off v hv).2).1
  obtain ⟨k₀', hk₀'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k₀ : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hw0]; exact hx1
    · exact (hoff0 v hv).le)
  set R : ℕ := (Algebra.norm ℤ k₀').natAbs with hR
  set q : ℕ := Ideal.absNorm w.asIdeal with hq
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set a : ℕ := q * (R + 1) + 1 with ha
  have hapos : 0 < a := Nat.succ_pos _
  have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
    intro h
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem h (w.asIdeal.mul_mem_right (((R + 1 : ℕ)) : 𝓞 E) hqmem)
      rw [ha] at this; push_cast at this; simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hwa : w.valuation E (a : E) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) a]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hanot

  obtain ⟨k, hkoff, hkw⟩ := hyp a hapos (x * x) ht0
  have hwk := hw_eq _ hkw
  have hk0 : (k : E) ≠ 0 := k.ne_zero
  have hoffk : ∀ v, v ≠ w → v.valuation E (k : E) = 1 ∧ v.valuation E ((k : E) - 1) ≤ 1 :=
    fun v hv => hoff a hapos _ hk0 v (hkoff v hv).1 (hkoff v hv).2
  obtain ⟨kk, hkk⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k : E) (fun v => by
    by_cases hv : v = w
    · subst hv; rw [hwk]; exact hx1
    · exact (hoffk v hv).1.le)

  obtain ⟨u, hu, hue⟩ := isUnit_of_valuation_eq_one ((k : E) / k₀) (div_ne_zero hk0 hk₀0) (fun v => by
    rw [map_div₀]
    by_cases hv : v = w
    · subst hv; rw [hw0, hwk, div_self hxpos]
    · rw [(hoffk v hv).1, hoff0 v hv, div_one])
  have hkku : kk = u * k₀' := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, hkk, hue, hk₀', div_mul_cancel₀ _ hk₀0]
  have hNk : (Algebra.norm ℤ kk).natAbs = R := by
    rw [hkku, map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 (hu.map _), one_mul]

  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (((k : E) - 1) / (a : E))
    (fun v => by
      by_cases hv : v = w
      · subst hv
        rw [map_div₀, hwa, div_one, ← hkk, ← map_one (algebraMap (𝓞 E) E), ← map_sub]
        exact v.valuation_le_one _
      · exact (hkoff v hv).1)
  have hkky : kk = 1 + (a : 𝓞 E) * y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    have ha0 : (a : E) ≠ 0 := Nat.cast_ne_zero.2 hapos.ne'
    rw [map_add, map_one, map_mul, map_natCast, hy, hkk]
    field_simp
    ring
  have hcong := norm_modEq_one a y
  rw [← hkky] at hcong
  have hdvd : (a : ℤ) ∣ Algebra.norm ℤ kk - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ a).1 (by rw [hcong, Int.cast_one])
  have hN1 : Algebra.norm ℤ kk = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    have hA : ((R : ℤ) + 2) ≤ (a : ℤ) := by
      rw [ha]; push_cast
      nlinarith [(Nat.one_le_cast (α := ℤ)).2 hqpos, (Nat.cast_nonneg R : (0 : ℤ) ≤ R)]
    have hR0 : (0 : ℤ) ≤ R := Nat.cast_nonneg R
    rcases Int.natAbs_eq (Algebra.norm ℤ kk) with h | h <;> rw [hNk] at h <;> rw [h] at hc ⊢
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith
    · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · subst hc0; linarith
      · nlinarith

  have hunit : IsUnit kk := by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton, hN1]
    rfl
  have hmem : kk ∈ w.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E kk) < 1
    rw [hkk, hwk]; exact hlt
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

end OrdZeroUnit
end GlobalTheory
