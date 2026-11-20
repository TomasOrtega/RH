import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Replace the relevant objects with their definitions. Both sides reduce to the same expression.
-/
theorem omegaK_eq (d : ℕ) : omegaK d = (1 + sqD d) / 2 := by
  unfold omegaK sqD
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities.

Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Take a linear combination of the given relations to obtain the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem KQ_mem_iff (d : ℕ) (z : ℂ) : z ∈ KQ d ↔ ∃ u v : ℚ, z = u + v * sqD d := by
  constructor
  · intro hz
    have h1 : z ∈ (KQ d).toSubalgebra := hz
    clear hz
    unfold KQ at h1
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (sqD_isIntegral d).isAlgebraic] at h1
    induction h1 using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
      have hs := sqD_sq d
      push_cast
      linear_combination (v * v') * hs
  · rintro ⟨u, v, rfl⟩
    have hs : sqD d ∈ KQ d := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    refine add_mem ?_ (mul_mem ?_ hs)
    · simp
    · simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ratInt_of_isIntegral {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, q = n := by
  have h1 : IsIntegral ℤ q := by
    rw [← isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective]
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨n, by rw [← hn]; simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem conj_sqD (d : ℕ) : (starRingEnd ℂ) (sqD d) = - sqD d := by
  unfold sqD
  simp

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem quadInt {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) :
    ∃ a b : ℤ, (((x : KQ d) : ℂ)) = a + b * omegaK d := by
  have hx : IsIntegral ℤ (((x : KQ d) : ℂ)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (IntermediateField.val (KQ d)).toRingHom.toIntAlgHom
  obtain ⟨u, v, huv⟩ := (KQ_mem_iff d _).mp (x : KQ d).2
  rw [huv] at hx
  have hc : IsIntegral ℤ ((starRingEnd ℂ) ((u : ℂ) + v * sqD d)) := hx.map (starRingEnd ℂ).toIntAlgHom
  rw [map_add, map_mul, conj_sqD, map_ratCast, map_ratCast] at hc
  have hs := sqD_sq d
  obtain ⟨A, hA⟩ := ratInt_of_isIntegral (q := 2 * u) (by
    have e : (((2 * u : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) + ((u : ℂ) + v * -sqD d) := by
      push_cast; ring
    rw [e]; exact hx.add hc)
  obtain ⟨N, hN⟩ := ratInt_of_isIntegral (q := u ^ 2 + d * v ^ 2) (by
    have e : (((u ^ 2 + d * v ^ 2 : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) * ((u : ℂ) + v * -sqD d) := by
      push_cast; linear_combination ((v : ℂ) ^ 2) * hs
    rw [e]; exact hx.mul hc)

  have hd0 : (d : ℤ) ≠ 0 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * v) = k := by
    set r : ℚ := (d : ℚ) * (2 * v) with hr
    have hr2 : r ^ 2 = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA]; ring
    have hden : r.den = 1 := by
      have := congrArg Rat.den hr2
      rw [Rat.den_pow, Rat.den_intCast] at this
      exact (Nat.pow_eq_one.mp this).resolve_right (by norm_num)
    exact ⟨r.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  have hk2 : k ^ 2 = d * (4 * N - A ^ 2) := by
    have : ((k ^ 2 : ℤ) : ℚ) = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hk, ← hN, ← hA]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := by
    have hsq : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsf
    exact (hsq.dvd_pow_iff_dvd (n := 2) (by norm_num)).mp ⟨_, hk2⟩
  obtain ⟨B, rfl⟩ := hdk
  have hB : 2 * v = B := by
    have : (d : ℚ) * (2 * v) = (d : ℚ) * B := by rw [hk]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this

  have h4 : A ^ 2 + (d : ℤ) * B ^ 2 = 4 * N := by
    have : ((A ^ 2 + (d : ℤ) * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA, ← hB]; ring
    exact_mod_cast this
  obtain ⟨c, hc3⟩ : ∃ c : ℤ, (d : ℤ) = 4 * c + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' A <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' B
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + 4 * c * b ^ 2 + 4 * c * b + c + 3 * b ^ 2 + 3 * b) + 3 := by
      rw [← h4]; ring
    omega
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + a + 4 * c * b ^ 2 + 3 * b ^ 2) + 1 := by
      rw [← h4]; ring
    omega
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring

end ReciprocityTheory.ChartRestriction.L1
