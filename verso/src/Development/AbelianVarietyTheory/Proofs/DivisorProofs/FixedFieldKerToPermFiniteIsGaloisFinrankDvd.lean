import Mathlib

open IntermediateField

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic Ω K := IsAlgClosure.isAlgebraic`. Use `haveI : Normal Ω K := IsAlgClosure.normal Ω K`. Use `haveI : IsGalois Ω K := ⟨⟩`. Use `set E : IntermediateField Ω K := fixedField φ.ker with hE`. Establish `hHF : φ.ker ≤ E.fixingSubgroup` using `(IntermediateField.le_iff_le _ _).1 le_rfl`.

Establish `hker : φ.ker.index ∣ n.factorial`. Rewrite using `[Subgroup.index_ker]`. Establish `h` using `Subgroup.card_subgroup_dvd_card φ.range`. Rewrite `h` using `[Nat.card_perm, Nat.card_fin]`. Then use the resulting hypothesis. Establish `hF : E.fixingSubgroup.index ∣ n.factorial` using `(Subgroup.index_dvd_of_le hHF).trans hker`.

Use `haveI : E.fixingSubgroup.FiniteIndex := ⟨fun h => (Nat.factorial_pos n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hF))⟩`. Establish `hopen : IsOpen (E.fixingSubgroup : Set (K ≃ₐ[Ω] K))` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (InfiniteGalois.fixingSubgroup_isClosed E)`. Use `haveI hfin : FiniteDimensional Ω E := (InfiniteGalois.isOpen_iff_finite E).1 hopen`. Establish `hnorm : E.fixingSubgroup.Normal`. Prove the components needed by the constructor for the conclusion.

Introduce `σ hσ g`. Rewrite `hσ`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `hx' : g⁻¹ x ∈ E`. Rewrite `hx`, the goal using `[hE, IntermediateField.mem_fixedField_iff]`.

Introduce `h hh`. Establish `hc : g * h * g⁻¹ ∈ φ.ker` using `(MonoidHom.normal_ker φ).conj_mem h hh g`. Use `hx _ hc` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `hσ _ hx'`.

Simplify using `only [AlgEquiv.mul_apply]`. Express the relevant statement in the definitionally equal form `g (σ (g⁻¹ x)) = x`. Rewrite using `[h2]`. Conclude with `g.apply_symm_apply x`. Use `haveI hgal : IsGalois Ω E := (InfiniteGalois.normal_iff_isGalois E).1 hnorm`.

Use `⟨hfin, hgal, ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `hF`.
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
