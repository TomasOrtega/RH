import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce a local definition for the expression. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem injective_of_surjective_endo {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩
  have hsurj : ∀ n, Function.Surjective (φ^[n]) := fun n => hφ.iterate n
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr
    (isNoetherianRing_iff.mp inferInstance) K
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ K (n + 1) := by
    show (φ ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  have h' : (φ ^ n) y = 0 := hy
  simpa [RingHom.coe_pow] using h'

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem psum_mem_range (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by
  refine ⟨X ⟨j - 1, by omega⟩, ?_⟩
  change powerSumHom N (X ⟨j - 1, by omega⟩) = _
  simp only [powerSumHom, aeval_X]
  congr 1
  show j - 1 + 1 = j
  omega

/- English proof (translation)
Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem esymm_mem_range (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hN := mul_esymm_eq_sum (Fin N) ℚ k
    have hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
      rw [hN]
      refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
      refine Subalgebra.sum_mem _ (fun a ha => ?_)
      obtain ⟨ha1', ha2⟩ := Finset.mem_filter.mp ha
      have ha1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
        (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))
    have hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k) := by
      rw [← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]
    rw [hinv]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_powerSumHom_eq {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩
  have h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q := by
    rw [← esymmAlgHom_apply, hQ]
  have h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range := by
    have hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤
        (powerSumHom N).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact esymm_mem_range N _ (by omega)
    exact hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)
  rw [h1]
  exact h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem powerSumHom_isSymmetric (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by
  have : powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ := by
    have hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ := by
      rintro _ ⟨T, rfl⟩
      simp only [powerSumHom]
      have : Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤
          symmetricSubalgebra (Fin N) ℚ := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact psum_isSymmetric (Fin N) ℚ _
      exact this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)
    exact hsub ⟨S, rfl⟩
  exact this

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem powerSumHom_injective (N : ℕ) : Function.Injective (powerSumHom N) := by

  let e := esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)
  let π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ :=
    (powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)
  let φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := e.symm.toAlgHom.comp π
  have hsurj : Function.Surjective φ := by
    intro T
    obtain ⟨S, hS⟩ := exists_powerSumHom_eq (e T).2
    refine ⟨S, ?_⟩
    apply e.injective
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact Subtype.ext hS
  have hinj : Function.Injective φ := injective_of_surjective_endo φ.toRingHom hsurj
  intro S T hST
  apply hinj
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hST

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem constantCoeff_powerSumHom (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by
  induction S using MvPolynomial.induction_on with
  | C a => simp [powerSumHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]
    simp [psum, constantCoeff_X]

end

end Flag

end RestTerms

end GroundTheory.Heights₂.Heights
