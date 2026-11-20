import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.TauW

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma xiV_eq_sum (k r : ℕ) (p : Fin r → ℂ) : xiV k r p = ∑ a, p a • bvec (eI k r a) := by
  ext i
  simp only [xiV, bvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val, h⟩]
    · rw [if_pos]
      ext
      simp [eI]
    · intro b _ hb
      rw [if_neg]
      intro he
      apply hb
      ext
      simp only [Fin.val_mk]
      have := congrArg Fin.val he
      simp [eI] at this
      omega
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro he
    apply h
    rw [he]
    simp [eI]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma fvec_castSucc' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    fvec k r z b.castSucc = bvec (eI k r b) := by
  simp [fvec]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma fvec_last' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma frame_sum' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    ∑ a, c a • fvec k r z a = ∑ b : Fin r, c b.castSucc • bvec (eI k r b) + c (Fin.last r) • z := by
  rw [Fin.sum_univ_castSucc]
  simp only [fvec_castSucc', fvec_last']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma bvec_eq_xiV (k r : ℕ) (b : Fin r) : bvec (eI k r b) = xiV k r (Pi.single b 1) := by
  rw [xiV_eq_sum]
  simp [Pi.single_apply, ite_smul]

end PI.PolynomialProperness.TauW

namespace PI.PolynomialProperness

open TauW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem tauMem_of (hMX : MXFacts) (hNE : NEFacts) : TauMem := by
  intro k r z hz v hv
  have hvX : v.submatrix Fin.castSucc Fin.castSucc ∈ UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij), fun i => hv.2 _⟩
  obtain ⟨hm1, hm2, hm3⟩ := hMX k r _ hvX
  obtain ⟨hn1, hn2, hn3⟩ := hNE k r z hz (fun a => v a.castSucc (Fin.last r))
  have hfr : ∀ b, tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    simp only [tauM]
    rw [← Matrix.mulVec_mulVec]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · rw [fvec_last', hm3 z hz.1, hn3, frame_sum', hv.2 (Fin.last r), one_smul, xiV_eq_sum]
      exact add_comm _ _
    · have h0 : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [fvec_castSucc', bvec_eq_xiV, hm2, hn2, frame_sum', xiV_eq_sum, h0, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Matrix.mulVec_single]
  exact ⟨WeylGroupFacts.mem_n_mul hn1 hm1, hfr, P.C2x5.uMap_eq hz _ _ hfr⟩

end PI.PolynomialProperness
