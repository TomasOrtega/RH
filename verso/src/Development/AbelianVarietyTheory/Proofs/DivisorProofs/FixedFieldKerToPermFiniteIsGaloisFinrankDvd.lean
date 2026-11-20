import Mathlib

open IntermediateField

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fixedField_ker_toPerm_finite_isGalois_finrank_dvd (Ω K : Type) [Field Ω] [Field K]
    [Algebra Ω K] [IsAlgClosure Ω K] [CharZero Ω] (n : ℕ)
    (φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin n)) :
    FiniteDimensional Ω (IntermediateField.fixedField φ.ker) ∧
      IsGalois Ω (IntermediateField.fixedField φ.ker) ∧
      Module.finrank Ω (IntermediateField.fixedField φ.ker) ∣ n.factorial := by
  haveI : Algebra.IsAlgebraic Ω K := IsAlgClosure.isAlgebraic
  haveI : Normal Ω K := IsAlgClosure.normal Ω K
  haveI : IsGalois Ω K := ⟨⟩
  set E : IntermediateField Ω K := fixedField φ.ker with hE
  have hHF : φ.ker ≤ E.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hker : φ.ker.index ∣ n.factorial := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hF : E.fixingSubgroup.index ∣ n.factorial :=
    (Subgroup.index_dvd_of_le hHF).trans hker
  haveI : E.fixingSubgroup.FiniteIndex :=
    ⟨fun h => (Nat.factorial_pos n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hF))⟩
  have hopen : IsOpen (E.fixingSubgroup : Set (K ≃ₐ[Ω] K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (InfiniteGalois.fixingSubgroup_isClosed E)
  haveI hfin : FiniteDimensional Ω E := (InfiniteGalois.isOpen_iff_finite E).1 hopen
  have hnorm : E.fixingSubgroup.Normal := by
    constructor
    intro σ hσ g
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ E := by
      rw [hE, IntermediateField.mem_fixedField_iff] at hx ⊢
      intro h hh
      have hc : g * h * g⁻¹ ∈ φ.ker := (MonoidHom.normal_ker φ).conj_mem h hh g
      have := hx _ hc
      calc h (g⁻¹ x) = g⁻¹ ((g * h * g⁻¹) x) := by simp [AlgEquiv.mul_apply]
        _ = g⁻¹ x := by rw [this]
    have h2 := hσ _ hx'
    simp only [AlgEquiv.mul_apply]
    change g (σ (g⁻¹ x)) = x
    rw [h2]
    exact g.apply_symm_apply x
  haveI hgal : IsGalois Ω E := (InfiniteGalois.normal_iff_isGalois E).1 hnorm
  refine ⟨hfin, hgal, ?_⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hF

end GlobalTheory
