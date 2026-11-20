import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4ResOfLine

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem psiRes0_ne {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (a : Fin (X.m + 1)) (h : WittVector.constantCoeff (g⁻¹ 0 a) ≠ 0) : psiRes0 X O S.w g a ≠ 0 := by
  intro h0
  unfold psiRes0 at h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have hu : IsUnit (g⁻¹ 0 a) := WittVector.isUnit_of_coeff_zero_ne_zero _ h
  have hu' : IsUnit (psiO X.p X.n' O 0 (g⁻¹ 0 a)) := hu.map _
  exact S.w_irr.not_isUnit (isUnit_of_dvd_unit h0 hu')

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem resLineAt : ResLineAt := by
  intro X _ O _ _ _ _ S _ _ g _ hne h0
  by_contra hall
  push_neg at hall
  apply hne
  have hcc : ∀ c : Fin X.m, WittVector.constantCoeff (g⁻¹ 0 c.succ) = 0 := by
    intro c
    by_contra hc
    exact psiRes0_ne S g c.succ hc (hall c)
  have hv0 : WittVector.constantCoeff (g⁻¹ 0 0) ≠ 0 := by
    intro hz
    apply h0
    unfold psiRes0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hx : g⁻¹ 0 0 = 0
    · rw [hx, map_zero]
      exact dvd_zero _
    · obtain ⟨m, b, hb, hab⟩ := WittVector.exists_eq_pow_p_mul (g⁻¹ 0 0) hx
      have hm : m ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hab
        exact hb (hab ▸ hz)
      rw [hab, map_mul, map_pow, map_natCast]
      have hwp : S.w ∣ (X.p : O) := by
        have h1 := S.p_mem
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr,
          Ideal.mem_span_singleton] at h1
        exact h1
      exact Dvd.dvd.mul_right (dvd_pow hwp hm) _
  have hset : ∀ h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'),
      ratPlane X.p X.n' 1 h =
        Submodule.span (GaloisField X.p X.n') {fun c => WittVector.constantCoeff (h⁻¹ 0 c)} := by
    intro h
    unfold ratPlane
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hi0]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [hset g, hset 1, inv_one]
  have hv : (fun c => WittVector.constantCoeff (g⁻¹ 0 c)) = WittVector.constantCoeff (g⁻¹ 0 0) •
      (fun c => WittVector.constantCoeff ((1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) 0 c)) := by
    funext c
    refine Fin.cases ?_ (fun c' => ?_) c
    · simp
    · simp [hcc c', Matrix.one_apply_ne (Fin.succ_ne_zero c').symm]
  rw [hv, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hv0)]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem loc4Res : LocalResidueBound := loc4Res_of_line resLineAt

end Formalism.MainNotions.ColumnSystems.Pf
