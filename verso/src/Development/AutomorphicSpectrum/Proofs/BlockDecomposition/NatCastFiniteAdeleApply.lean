import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF
open WithZero Multiplicative

namespace GlobalTheory.CompanionTheory.EisTF

variable {k : Type} [Field k] [NumberField k]

/- English proof (translation)
Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem natCast_finiteAdele_apply (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    ((M : FiniteAdeleRing (𝓞 k) k) v) = (M : v.adicCompletion k) := by
  induction M with
  | zero => simp only [Nat.cast_zero]; rfl
  | succ m ih =>
    simp only [Nat.cast_succ]
    change ((m : FiniteAdeleRing (𝓞 k) k) v) + (1 : FiniteAdeleRing (𝓞 k) k) v = _
    rw [ih]
    rfl

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    Valued.v (M : v.adicCompletion k) ≤ 1 := by
  have : (M : v.adicCompletion k) ∈ v.adicCompletionIntegers k := natCast_mem _ M
  exact this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valued_absNorm_lt_one (v : HeightOneSpectrum (𝓞 k)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) < 1 := by
  have hv : ∀ x : k, Valued.v (algebraMap k (v.adicCompletion k) x) = v.valuation k x :=
    fun x => v.valuedAdicCompletion_eq_valuation' x
  have h : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h2 := (v.valuation_lt_one_iff_mem (K := k) _).2 h
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) =
      algebraMap k (v.adicCompletion k) (algebraMap (𝓞 k) k ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k)) := by
    simp
  rw [h3, hv]
  exact h2

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = exp a := ⟨log x, (exp_log hx).symm⟩
    rw [← exp_zero, exp_lt_exp] at h
    rw [exp_le_exp]
    omega

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules.
-/
theorem valued_absNorm_pow_le (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (((Ideal.absNorm v.asIdeal ^ n : ℕ)) : v.adicCompletion k) ≤ exp (-(n : ℤ)) := by
  have h1 := le_exp_neg_one_of_lt_one (valued_absNorm_lt_one v)
  rw [Nat.cast_pow, map_pow]
  refine (pow_le_pow_left₀ zero_le' h1 n).trans (le_of_eq ?_)
  rw [← exp_nsmul]
  congr 1
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem valued_prod_le (S : Finset (HeightOneSpectrum (𝓞 k))) (n : HeightOneSpectrum (𝓞 k) → ℕ)
    {v : HeightOneSpectrum (𝓞 k)} (hv : v ∈ S) :
    Valued.v (((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ)) : v.adicCompletion k) ≤ exp (-(n v : ℤ)) := by
  classical
  rw [← Finset.mul_prod_erase S _ hv, Nat.cast_mul, map_mul]
  calc _ ≤ Valued.v (((Ideal.absNorm v.asIdeal ^ n v : ℕ)) : v.adicCompletion k) * 1 :=
        mul_le_mul_right (valued_natCast_le_one v _) _
    _ ≤ exp (-(n v : ℤ)) := by rw [mul_one]; exact valued_absNorm_pow_le v (n v)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem condM : CondM := by
  intro k _ _ ω
  let χ : (FiniteAdeleRing (𝓞 k) k)ˣ →* Circle := ω.toIdele.comp ofFinite
  have hχ : Continuous χ := ω.continuous_toIdele.comp continuous_ofFinite
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker_circle χ hχ
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ?_
    exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rintro u hu ⟨y, hy, huy⟩
    have hmem : u ∈ finiteLevel n := by
      refine mem_finiteLevel.2 fun v => ?_
      have hz : finiteComponent v u ∈ unitsLevel (K := k) v 0 := by
        rw [unitsLevel_zero, Submonoid.mem_units_iff]
        exact (mem_finiteIntegralUnits k).1 hu v
      by_cases hv : v ∈ S
      · refine mem_unitsLevel.2 ⟨(mem_unitsLevel.1 hz).1, ?_⟩
        have hyv : Valued.v (y v) ≤ 1 := mem_integralFiniteAdeles.1 hy v
        have huv : ((u : FiniteAdeleRing (𝓞 k) k) v) - 1 =
            ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * y v := by
          have := congrArg (fun x : FiniteAdeleRing (𝓞 k) k => x v) huy
          rw [← natCast_finiteAdele_apply]
          exact this
        rw [coe_finiteComponent, huv, map_mul]
        calc _ ≤ Valued.v ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * 1 :=
              mul_le_mul_right hyv _
          _ ≤ _ := by rw [mul_one]; exact valued_prod_le S n hv
      · rw [h0 v hv]
        exact hz
    exact MonoidHom.mem_ker.1 (hker hmem)

end GlobalTheory.CompanionTheory.EisTF
