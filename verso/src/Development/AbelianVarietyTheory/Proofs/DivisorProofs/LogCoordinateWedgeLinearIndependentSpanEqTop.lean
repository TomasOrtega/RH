import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

/- English proof (translation)
Use `show s.orderEmbOfFin rfl ⟨k, hk⟩ = _`. Rewrite using `[Finset.orderEmbOfFin_apply]`. Both sides reduce to the same expression.
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
Rewrite using `[dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]`. Both sides reduce to the same expression.
-/
theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, logWedge]`. Use `congr 1`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Introduce `k h1 h2`. Simplify using `only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]`. Rewrite using `[ofCard_symm_apply_eq_sort]`.
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
Introduce `K _ n x hx`. Rewrite using `[logWedge_eq_basis x hx]`. Conclude with `⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩`.
-/
theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
