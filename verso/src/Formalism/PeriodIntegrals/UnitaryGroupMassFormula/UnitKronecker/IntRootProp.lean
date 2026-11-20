import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development

namespace PI.UnitKronW

open Polynomial NumberField

def IntRootProp : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
    ∀ x : L, (p.map (algebraMap E L)).IsRoot x → IsIntegral ℤ x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem stepB_of (hI : IntRootProp) : StepB := by
  intro E _ _ p hp hc hnorm φ₀ μ hμ
  have h1 : eval₂ φ₀ μ p = 0 := by rw [← eval_map]; exact hμ
  obtain ⟨q, hq0, hirr, hqp, hqμ⟩ : ∃ q : E[X], q ≠ 0 ∧ Irreducible q ∧ q ∣ p ∧ eval₂ φ₀ μ q = 0 := by
    letI : Algebra E ℂ := φ₀.toAlgebra
    have hμa : aeval μ p = 0 := by rw [aeval_def]; exact h1
    have hint_r : IsIntegral E μ := ⟨p, hp, h1⟩
    refine ⟨minpoly E μ, minpoly.ne_zero hint_r, minpoly.irreducible hint_r, minpoly.dvd E μ hμa, ?_⟩
    have h3 := minpoly.aeval E μ
    rw [aeval_def] at h3
    exact h3
  haveI : Fact (Irreducible q) := ⟨hirr⟩
  haveI : Module.Finite E (AdjoinRoot q) := Module.Finite.of_basis (AdjoinRoot.powerBasis hq0).basis
  haveI : NumberField (AdjoinRoot q) := NumberField.of_module_finite E (AdjoinRoot q)
  have hx : (p.map (algebraMap E (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    show eval (AdjoinRoot.root q) (p.map (algebraMap E (AdjoinRoot q))) = 0
    rw [eval_map, AdjoinRoot.algebraMap_eq]
    obtain ⟨r, hr⟩ := hqp
    rw [hr, eval₂_mul, AdjoinRoot.eval₂_root, zero_mul]
  have hxint : IsIntegral ℤ (AdjoinRoot.root q) := hI E (AdjoinRoot q) p hp hc _ hx
  have hxn : ∀ ψ : AdjoinRoot q →+* ℂ, ‖ψ (AdjoinRoot.root q)‖ = 1 := by
    intro ψ
    apply hnorm (ψ.comp (algebraMap E (AdjoinRoot q))) (ψ (AdjoinRoot.root q))
    have h2 : eval₂ (algebraMap E (AdjoinRoot q)) (AdjoinRoot.root q) p = 0 := by
      rw [← eval_map]; exact hx
    show eval (ψ (AdjoinRoot.root q)) (p.map (ψ.comp (algebraMap E (AdjoinRoot q)))) = 0
    rw [eval_map, ← hom_eval₂, h2, map_zero]
  obtain ⟨n, hn, hxpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := AdjoinRoot q) (A := ℂ) hxint hxn
  refine ⟨n, hn, ?_⟩
  calc μ ^ n = (AdjoinRoot.lift φ₀ μ hqμ (AdjoinRoot.root q)) ^ n := by rw [AdjoinRoot.lift_root]
    _ = 1 := by rw [← map_pow, hxpow, map_one]

end PI.UnitKronW

namespace PI.UnitKronW

open Polynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intRootProp : IntRootProp := by
  intro E L _ _ _ p hp hc x hx
  have hcoef : ∀ n, (p.map (algebraMap E L)).coeff n ∈
      Set.range (algebraMap (integralClosure ℤ L) L) := by
    intro n
    rw [coeff_map]
    have hmem : algebraMap E L (p.coeff n) ∈ integralClosure ℤ L := by
      rw [mem_integralClosure_iff]
      exact (hc n).map (algebraMap E L).toIntAlgHom
    exact ⟨⟨algebraMap E L (p.coeff n), hmem⟩, rfl⟩
  obtain ⟨r, hr, -, hrm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts _).mpr hcoef) (hp.map (algebraMap E L))
  have hxS : IsIntegral (integralClosure ℤ L) x := by
    refine ⟨r, hrm, ?_⟩
    rw [← eval_map, hr]
    exact hx
  exact isIntegral_trans x hxS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepB : StepB :=
  stepB_of intRootProp

end PI.UnitKronW
