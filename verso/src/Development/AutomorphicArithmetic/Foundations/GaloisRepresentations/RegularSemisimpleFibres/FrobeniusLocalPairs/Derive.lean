import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import GroundTheory.LocalFields.Uniqueness

noncomputable section

open ValuativeRel

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

/- English proof (translation)
Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
private theorem mem_int' (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  have hx := x.2
  rw [Valuation.mem_integer_iff] at hx ⊢
  rwa [GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules.

Treat this case separately. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem pow_red' (h : IsRes rk rK s sb) (j : ℕ) (x y : 𝒪[K]) (hy : (y : K) = (s ^ j) x) :
    rK y = (sb ^ j) (rK x) := by
  induction j generalizing y with
  | zero =>
    have hyx : y = x := Subtype.ext (by simpa using hy)
    subst hyx
    simp
  | succ j ih =>
    let z : 𝒪[K] := ⟨(s ^ j) x, mem_int' (s ^ j) x⟩
    have hz : rK z = (sb ^ j) (rK x) := ih z rfl
    have hyz : (y : K) = s (z : K) := by
      rw [hy, pow_succ']
      rfl
    rw [h.gal z y hyz, hz, pow_succ']
    rfl

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem finrank_dvd' [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  classical
  haveI : Algebra.IsAlgebraic F₀ F₁ := Algebra.IsAlgebraic.of_finite F₀ F₁
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z]
    rfl
  have hone : sb ^ orderOf s = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := h.onto₁ w
    have := pow_red' h (orderOf s) x x (by rw [pow_orderOf_eq_one]; rfl)
    rw [AlgEquiv.one_apply, ← this]
  rw [← h.deg, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁, ← hsb]
  exact orderOf_dvd_of_pow_eq_one hone

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
private theorem isGalois_of_isRes [Fintype F₁] (h : IsRes rk rK s sb) : IsGalois k K := by
  classical
  have hd := finrank_dvd' h
  have hpos : 0 < orderOf s := orderOf_pos s
  have hle1 : orderOf s ≤ Fintype.card (K ≃ₐ[k] K) := orderOf_le_card_univ
  have hle2 : Fintype.card (K ≃ₐ[k] K) ≤ Module.finrank k K := AlgEquiv.card_le
  have hle3 : Module.finrank k K ≤ orderOf s := Nat.le_of_dvd hpos hd
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.derive :
    UpperTheory.Gal.InertialTypesAlt.L.Derive := by
  intro k K _ _ _ _ _ _ _ _ _ hc F₀ F₁ _ _ _ _ _ rk rK s sb h
  haveI hv : ValuativeExtension k K := GlobalTheory.LBC.Inh.valuativeExtension hc
  have hpos : 0 < Module.finrank k K := by
    rw [← h.deg]
    exact Module.finrank_pos
  haveI hf : FiniteDimensional k K := Module.finite_of_finrank_pos hpos
  exact ⟨hv, hf, isGalois_of_isRes h⟩
