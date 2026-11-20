import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FrobeniusRankParts

noncomputable section

namespace GlobalTheory.ParamRepCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations
open scoped Pointwise

section Inertia

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
/- English proof (translation)
Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← B.valuation_le_one_iff, map_inv₀]`. Establish `h0 : 0 < B.valuation y`. Rewrite using `[zero_lt_iff]`.

Conclude with `(Valuation.ne_zero_iff _).2 hy`. Simplify using `[hy, inv_le_one₀ h0]`.
-/
private lemma valuation_lt_one_iff_eq_zero_or_inv_notMem' (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← B.valuation_le_one_iff, map_inv₀]
    have h0 : 0 < B.valuation y := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hy
    simp [hy, inv_le_one₀ h0]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
/- English proof (translation)
Use `⟨fun hy => ?_, ValuationSubring.smul_mem_pointwise_smul h y B⟩` and prove the remaining obligations. Use `ValuationSubring.smul_mem_pointwise_smul h⁻¹ _ _ hy` as an intermediate fact. Simplify `this` using `[smul_smul]`.
-/
private lemma smul_mem_smul_valuationSubring_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    h • y ∈ h • B ↔ y ∈ B := by
  refine ⟨fun hy => ?_, ValuationSubring.smul_mem_pointwise_smul h y B⟩
  have := ValuationSubring.smul_mem_pointwise_smul h⁻¹ _ _ hy
  simpa [smul_smul] using this

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
/- English proof (translation)
Rewrite using `[valuation_lt_one_iff_eq_zero_or_inv_notMem', valuation_lt_one_iff_eq_zero_or_inv_notMem', ← smul_inv'', smul_mem_smul_valuationSubring_iff]`. Simplify using the standard rewrite rules.
-/
private lemma valuation_smul_smul_lt_one_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    (h • B).valuation (h • y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem', valuation_lt_one_iff_eq_zero_or_inv_notMem', ← smul_inv'',
    smul_mem_smul_valuationSubring_iff]
  simp

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in

/- English proof (translation)
Substitute `hg` using the available equality. Take `⟨hdec, hval⟩` from `hσ`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hdec`, the goal using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Rewrite using `[mul_smul, mul_smul, hdec, inv_smul_smul]`.

Rewrite using `[← valuation_smul_smul_lt_one_iff g]`. Establish `hx' : (g • A).valuation (g • x) ≤ 1`. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul g x A hx`. Use `hval (g • x) hx'` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Simplify using `[AlgEquiv.smul_def]`.
-/
theorem _root_.GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq {A A' : ValuationSubring Ω} {g σ : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : g • A = A') (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A') : g⁻¹ * σ * g ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A := by
  subst hg
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    rw [mul_smul, mul_smul, hdec, inv_smul_smul]
  · rw [← valuation_smul_smul_lt_one_iff g]
    have hx' : (g • A).valuation (g • x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact ValuationSubring.smul_mem_pointwise_smul g x A hx
    have := hval (g • x) hx'
    convert this using 2
    rw [smul_sub]
    simp [AlgEquiv.smul_def]

end Inertia

section Clauses

variable (D : D7)

end Clauses

end GlobalTheory.ParamRepCompare

end
