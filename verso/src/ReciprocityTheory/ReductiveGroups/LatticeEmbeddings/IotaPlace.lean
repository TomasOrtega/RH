import Mathlib
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB

noncomputable section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.ChartRestriction.B3.IotaPl

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hsum := hf.as_sum
  rw [hsum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hfx
  have key : x ^ n = -∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hfx
  have hx1 : 1 ≤ ‖x‖ := hlt.le
  have bound : ‖∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i)‖ ≤
        ‖x‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
      first
        | (simpa using h)
        | (rw [algebraMap_int_eq, eq_intCast]; exact h)
        | (convert h using 2; exact (algebraMap ℤ ℂ_[p]).eq_intCast _)
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h2 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact bound
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at key
    simp at key
  · have h3 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
    linarith

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 := by
  obtain ⟨f, hf, hfy⟩ := NumberField.RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegral_int ⟨f, hf, ?_⟩
  have e : (algebraMap ℤ ℂ_[p]) = ι.comp (algebraMap ℤ K) := RingHom.ext_int _ _
  rw [e, ← Polynomial.hom_eval₂, hfy, map_zero]

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 K) ∈ smallIdeal ι := (Ideal.eq_top_iff_one _).mp h
    rw [mem_smallIdeal] at h1
    simp at h1
  · intro a b hab
    simp only [mem_smallIdeal] at hab ⊢
    have e : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [e, norm_mul] at hab
    by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    nlinarith [norm_int_le ι a, norm_int_le ι b]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have e : (p : ℂ_[p]) = (((algebraMap ℚ_[p] (PadicAlgCl p)) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    first
      | simp
      | (rw [map_natCast]; exact (map_natCast UniformSpace.Completion.coeRingHom p).symm)
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p_lt_one
    | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    | (rw [padicNormE.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))

def vAdd (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)

end ReciprocityTheory.ChartRestriction.B3.IotaPl

namespace ReciprocityTheory.ChartRestriction.B3

end ReciprocityTheory.ChartRestriction.B3
