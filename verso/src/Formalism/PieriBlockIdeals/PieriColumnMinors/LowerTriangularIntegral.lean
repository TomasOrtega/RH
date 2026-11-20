import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lre_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem lre_le_apply {s r : ℕ} (I : Fin s → Fin r) (hI : StrictMono I) (p : Fin s) : p.val ≤ (I p).val := by
  obtain ⟨k, hk⟩ := p
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : I ⟨k, by omega⟩ < I ⟨k + 1, hk⟩ := hI (by simp [Fin.lt_def])
    have h3 : (I ⟨k, by omega⟩).val < (I ⟨k + 1, hk⟩).val := h2
    show k + 1 ≤ (I ⟨k + 1, hk⟩).val
    have h1' : k ≤ (I ⟨k, by omega⟩).val := h1
    omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem lre_lowerTri {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r)
    (hI : ∀ k, StrictMono (I k)) : LowerTri (bidetExp sz hsz I) := by
  intro a s has
  unfold bidetExp
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h
  have h1 : I k p = a := congrArg Prod.fst h
  have h2 : Fin.castLE (hsz k) p = s := congrArg Prod.snd h
  have h3 := lre_le_apply (I k) (hI k) p
  have h4 : p.val = s.val := by rw [← h2]; rfl
  rw [h1] at h3
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem lower_triangular_integral : LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ Q ∈ dualWeyl ℚ r n ν,
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      (colLex r n).toSyn ((colLex r n).degree Q) = d →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact key _ Q hQ hint rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hz hd
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hbmap : bideterminant ℚ sz hsz I = intQ r n (bideterminant ℤ sz hsz I) := by
      rw [lre_intQ_apply, ldlat_map_bidet]
    have hbmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rw [hshape] at this
      exact this
    have hmL : LowerTri m := by
      rw [← hexp]
      exact lre_lowerTri sz hsz I hmono
    obtain ⟨c, hc⟩ := hz m hmL
    have hlc : (colLex r n).leadingCoeff f = (c : ℚ) := hc
    have hf'mem : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbmem)
    have hf'z : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e →
        ∃ z : ℤ, coeff e (f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I) = z := by
      intro e he
      obtain ⟨z, hz'⟩ := hz e he
      refine ⟨z - c * coeff e (bideterminant ℤ sz hsz I), ?_⟩
      rw [coeff_sub, coeff_smul, hz', hlc, hbmap, lre_intQ_apply, coeff_map]
      simp
    have hfin : ∃ Q'' : MvPolynomial (Fin r × Fin n) ℤ,
        f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n Q'' := by
      by_cases h0 : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hbdeg.trans hexp) hblc h0
        exact ih _ (hd ▸ hlt) _ hf'mem hf'z rfl
    obtain ⟨Q'', hQ''⟩ := hfin
    refine ⟨Q'' + c • bideterminant ℤ sz hsz I, ?_⟩
    rw [map_add, map_smul, ← hQ'', ← hbmap, hlc, Int.cast_smul_eq_zsmul]
    abel

end Formalism.CohomologicalDescent.LR
