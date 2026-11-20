import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ofCard_symm_apply_eq_sort {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k < s.card) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card)) ⟨k, hk⟩ =
      (s.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; exact hk) := by
  show s.orderEmbOfFin rfl ⟨k, hk⟩ = _
  rw [Finset.orderEmbOfFin_apply]
  rfl

noncomputable def dlogBasis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    Module.Basis (Fin n) K Ω[K⁄ℤ] :=
  (Module.Basis.mk hx.1 (by rw [hx.2])).unitsSMul fun i => (x i)⁻¹

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem logWedge_eq_basis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    logWedge x = ⇑(dlogBasis x hx).ExteriorAlgebra := by
  funext s
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    logWedge]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]
    rw [ofCard_symm_apply_eq_sort]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
