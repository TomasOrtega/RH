import Mathlib

noncomputable section

namespace PI.GoodTwo.AlgebraicValuationTrichotomy

open NumberField QuadraticAlgebra

abbrev Kq (m : ℕ) := QuadraticAlgebra ℚ (-(m : ℚ)) 1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem noRoot (m : ℕ) (hm : 1 ≤ m) : ∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r := by
  intro r h
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg (r - 1 / 2)]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem sqfree_rat (d : ℕ) (hd : Squarefree d) (q : ℚ) (k : ℤ) (h : (d : ℚ) * q ^ 2 = k) :
    ∃ y : ℤ, q = y := by
  have h1 : ((d : ℤ) * q.num ^ 2 : ℚ) = ((k * (q.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    rw [← Rat.mul_den_eq_num]
    push_cast
    rw [← h]
    ring
  have h1' : (d : ℤ) * q.num ^ 2 = k * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
  have h2 : ((q.den : ℤ) ^ 2) ∣ (d : ℤ) * q.num ^ 2 := ⟨k, by rw [h1']; ring⟩
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Int.isCoprime_iff_gcd_eq_one.2 (by rw [Int.gcd_comm]; exact q.reduced)).pow
  have h3 : ((q.den : ℤ) ^ 2) ∣ (d : ℤ) := hcop.dvd_of_dvd_mul_right h2
  have h4 : q.den ^ 2 ∣ d := by exact_mod_cast h3
  have hden : q.den = 1 := Nat.isUnit_iff.1 (hd q.den (by simpa [sq] using h4))
  exact ⟨q.num, by rw [← Rat.mul_den_eq_num, hden]; simp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem rat_int_of_integral (q : ℚ) (h : IsIntegral ℤ q) : ∃ n : ℤ, q = n := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨n, by rw [← hn, eq_intCast]⟩

section
variable (m : ℕ) [Fact (∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r)]

instance : NumberField (Kq m) := {}

/- English proof (translation)
A detailed English derivation is pending.
-/
example : Fintype (ClassGroup (𝓞 (Kq m))) := inferInstance

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isIntegral_omega : IsIntegral ℤ (ω : Kq m) := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C (m : ℤ) - Polynomial.X), Polynomial.monic_X_pow_add ?_, ?_⟩
  · exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (by compute_degree!)) (by norm_num)
  · simp [QuadraticAlgebra.ext_iff, sq]

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isIntegral_mk (x y : ℤ) : IsIntegral ℤ (⟨x, y⟩ : Kq m) := by
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : Kq m) := fun n => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ (Kq m) n))
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, Algebra.smul_def, map_intCast, map_intCast]
  exact (hint x).add ((hint y).mul (isIntegral_omega m))

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem repr_int (d : ℕ) (hd : Squarefree d) (hdm : d + 1 = 4 * m) (z : Kq m)
    (hz : IsIntegral ℤ z) : ∃ x y : ℤ, z = ⟨x, y⟩ := by
  obtain ⟨a, b⟩ := z
  have hstar : IsIntegral ℤ (star (⟨a, b⟩ : Kq m)) := hz.map (starRingEnd (Kq m)).toIntAlgHom
  have hinj : Function.Injective (algebraMap ℚ (Kq m)) := (algebraMap ℚ (Kq m)).injective
  have ht : IsIntegral ℤ (2 * a + b) := by
    have h := hz.add hstar
    have e : (⟨a, b⟩ : Kq m) + star ⟨a, b⟩ = algebraMap ℚ (Kq m) (2 * a + b) := by
      ext <;> simp [QuadraticAlgebra.star_mk] <;> ring_nf
    rw [e] at h
    exact (isIntegral_algebraMap_iff hinj).1 h
  have hn : IsIntegral ℤ (a ^ 2 + a * b + m * b ^ 2) := by
    have h := hz.mul hstar
    have e : (⟨a, b⟩ : Kq m) * star ⟨a, b⟩ = algebraMap ℚ (Kq m) (a ^ 2 + a * b + m * b ^ 2) := by
      rw [QuadraticAlgebra.mul_star]
      simp only [← map_mul, ← map_add, ← map_sub]
      congr 1
      ring
    rw [e] at h
    exact (isIntegral_algebraMap_iff hinj).1 h
  obtain ⟨T, hT⟩ := rat_int_of_integral _ ht
  obtain ⟨N, hN⟩ := rat_int_of_integral _ hn
  have hd' : (d : ℚ) = 4 * m - 1 := by
    have h1 : (d : ℚ) + 1 = 4 * m := by exact_mod_cast hdm
    linarith
  obtain ⟨B, hB⟩ := sqfree_rat d hd b (4 * N - T ^ 2) (by
    push_cast
    rw [← hT, ← hN, hd']
    ring)
  have hZ : (4 * N : ℤ) = T ^ 2 + (4 * m - 1) * B ^ 2 := by
    have h1 : ((4 * N : ℤ) : ℚ) = ((T ^ 2 + (4 * m - 1) * B ^ 2 : ℤ) : ℚ) := by
      push_cast
      rw [← hT, ← hN, hB]
      ring
    exact_mod_cast h1
  have hev : Even ((T - B) * (T + B)) := ⟨2 * (N - m * B ^ 2), by linear_combination (-1 : ℤ) * hZ⟩
  have hevTB : Even (T - B) := by
    rcases Int.even_mul.1 hev with h | h
    · exact h
    · have e : T - B = (T + B) - 2 * B := by ring
      rw [e]
      exact h.sub (even_two_mul B)
  obtain ⟨k, hk⟩ := hevTB
  refine ⟨k, B, ?_⟩
  have ha : a = k := by
    have h1 : (T : ℚ) - B = k + k := by exact_mod_cast hk
    rw [← hT, hB] at h1
    linarith
  rw [ha, hB]

end

end PI.GoodTwo.AlgebraicValuationTrichotomy
