import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Generate

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem two_pow_dvd_intCast_padic_iff (k : ℤ) (n : ℕ) : (2 : ℤ_[2]) ^ n ∣ (k : ℤ_[2]) ↔ (2 : ℤ) ^ n ∣ k := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (k : ℤ_[2]) n).symm.trans
    (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := k) (n := n))
  rw [Ideal.mem_span_singleton] at h
  exact_mod_cast h

/- English proof (translation)
Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
private theorem index_closed_dyadic_subgroup (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p a : ℕ) (hH : IsClosed (H : Set ℤ_[2]ˣ))
    (hu : u ∈ H) (hp : (u : ℤ_[2]) = p) (ha : 2 ≤ a) (h1 : (2 : ℤ) ^ a ∣ (p : ℤ) ^ 2 - 1)
    (h2 : ¬ (2 : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ 2 - 1) (h3 : ¬ (2 : ℤ) ^ a ∣ (p : ℤ) - 1) :
    H.index ≠ 0 ∧ 2 * H.index ≤ Nat.totient (2 ^ a) := by
  have hu2 : ((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = (((p : ℤ) ^ 2 - 1 : ℤ) : ℤ_[2]) := by
    push_cast [Units.val_pow_eq_pow_val, hp]
    ring
  have hem : emultiplicity ((2 : ℕ) : ℤ_[2]) (((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1) = (a : ℕ∞) := by
    rw [emultiplicity_eq_coe, hu2]
    simp only [Nat.cast_ofNat, two_pow_dvd_intCast_padic_iff]
    exact ⟨h1, h2⟩
  have hle : KStar.TotallyRealRoots.princ 2 a ≤ H :=
    KStar.TotallyRealRoots.princ_le_of_isClosed (by omega) (fun _ => ha) hH (H.pow_mem hu 2) hem
  have hnot : u ∉ KStar.TotallyRealRoots.princ 2 a := by
    rw [KStar.TotallyRealRoots.mem_princ, hp]
    intro h
    apply h3
    rw [← two_pow_dvd_intCast_padic_iff]
    exact_mod_cast h
  have hidx : (KStar.TotallyRealRoots.princ 2 a).index ≤ Nat.totient (2 ^ a) := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_le_card_group _
  have hpos : 0 < (KStar.TotallyRealRoots.princ 2 a).index := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker]
    exact Nat.card_pos
  have hr := Subgroup.relIndex_mul_index hle
  have hr1 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h hu)
  have hr0 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    omega
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, mul_zero] at hr
    omega
  · calc 2 * H.index ≤ (KStar.TotallyRealRoots.princ 2 a).relIndex H * H.index :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (KStar.TotallyRealRoots.princ 2 a).index := hr
      _ ≤ Nat.totient (2 ^ a) := hidx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Substitute using the available equality.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable.

Assume the hypotheses and unpack their components. Evaluate the numerical expressions. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Move the embeddings inside the algebraic operations. Evaluate the numerical expressions. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Substitute using the available equality.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable.

Assume the hypotheses and unpack their components. Evaluate the numerical expressions. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Move the embeddings inside the algebraic operations. Evaluate the numerical expressions. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Two.idxAdic :
    ∀ (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p c : ℕ), IsClosed (H : Set ℤ_[2]ˣ) → u ∈ H → (u : ℤ_[2]) = p → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → H.index ≠ 0 ∧ H.index ≤ c := by
  intro H u p c hH hu hp hpc
  rcases hpc with ⟨hp8, rfl⟩ | ⟨hp16, rfl⟩
  · have hk : p = 8 * (p / 8) + 3 := by omega
    generalize p / 8 = k at hk
    subst hk
    have e : ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 = 16 * (4 * (k : ℤ) ^ 2 + 3 * k) + 8 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (3 + 1) ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (8 * k + 3) 3 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 3) = 4 := by decide
    omega
  · have hk : p = 16 * (p / 16) + 7 := by omega
    generalize p / 16 = k at hk
    subst hk
    have e : ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 = 32 * (8 * (k : ℤ) ^ 2 + 7 * k + 1) + 16 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (4 + 1) ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (16 * k + 7) 4 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 4) = 8 := by decide
    omega
