import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

noncomputable section

namespace GlobalTheory.K5.ReprSpan

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isAlgZp_one : IsAlgZp p (1 : Ω) :=
  ⟨X - C 1, X_sub_C_ne_zero 1, by simp⟩

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp p x) (hy : IsAlgZp p y) : IsAlgZp p (x * y) := by
  letI : Algebra ℤ_[p] Ω := Algebra.compHom Ω (algebraMap ℤ_[p] (O0 p))
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp p z ↔ IsAlgebraic ℤ_[p] z := fun z => by
    simp only [IsAlgZp, IsAlgebraic, aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

variable (p Ω) in

def algZpMonoid : Submonoid Ω where
  carrier := {x | IsAlgZp p x}
  one_mem' := isAlgZp_one
  mul_mem' := isAlgZp_mul

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem mem_adjoin_iff (z : Ω) :
    z ∈ Algebra.adjoin (O0 p) {x : Ω | IsAlgZp p x} ↔
      z ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x} := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure {x : Ω | IsAlgZp p x} : Set Ω) = {x | IsAlgZp p x} := by
    rw [show {x : Ω | IsAlgZp p x} = (algZpMonoid p Ω : Set Ω) from rfl, Submonoid.closure_eq]
  rw [hcl]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_mul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x} := by
  intro p _ Ω _ _ h b hb
  set B := Algebra.adjoin (O0 p) {x : Ω | IsAlgZp p x} with hBdef
  let S : Subfield Ω :=
    { carrier := {b | ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ B}
      zero_mem' := ⟨1, one_ne_zero, by rw [mul_zero]; exact B.zero_mem⟩
      one_mem' := ⟨1, one_ne_zero, by rw [map_one, mul_one]; exact B.one_mem⟩
      add_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a + c) =
            algebraMap (O0 p) Ω g' * (algebraMap (O0 p) Ω g * a) +
              algebraMap (O0 p) Ω g * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) ha) (B.mul_mem (B.algebraMap_mem _) hc)
      mul_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a * c) =
            (algebraMap (O0 p) Ω g * a) * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.mul_mem ha hc
      neg_mem' := by
        rintro a ⟨g, hg, ha⟩
        exact ⟨g, hg, by rw [mul_neg]; exact B.neg_mem ha⟩
      inv_mem' := by
        rintro a ⟨g, hg, ha⟩
        by_cases ha0 : a = 0
        · exact ⟨1, one_ne_zero, by rw [ha0, inv_zero, mul_zero]; exact B.zero_mem⟩
        have hg0 : algebraMap (O0 p) Ω g ≠ 0 := fun e => hg (h.inj (by rw [e, map_zero]))
        have hy0 : algebraMap (O0 p) Ω g * a ≠ 0 := mul_ne_zero hg0 ha0
        let y : B := ⟨algebraMap (O0 p) Ω g * a, ha⟩
        have halg : IsAlgebraic (O0 p) y :=
          (isAlgebraic_algHom_iff B.val Subtype.val_injective).1 (h.alg.isAlgebraic _)
        have hnz : y ∈ nonZeroDivisors B :=
          mem_nonZeroDivisors_of_ne_zero (fun e => hy0 (congrArg Subtype.val e))
        obtain ⟨r, hr, s, hs⟩ := halg.exists_nonzero_dvd hnz
        have hs' : algebraMap (O0 p) Ω r = algebraMap (O0 p) Ω g * a * (s : Ω) := by
          have := congrArg Subtype.val hs
          simpa [y] using this
        refine ⟨r, hr, ?_⟩
        have e : algebraMap (O0 p) Ω r * a⁻¹ = algebraMap (O0 p) Ω g * (s : Ω) := by
          rw [hs']; field_simp
        show algebraMap (O0 p) Ω r * a⁻¹ ∈ B
        rw [e]
        exact B.mul_mem (B.algebraMap_mem g) s.2 }
  have hle : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}) ≤ S := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact B.algebraMap_mem c⟩
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  obtain ⟨g, hg, hgb⟩ := hle hb
  exact ⟨g, hg, (mem_adjoin_iff _).1 hgb⟩

end GlobalTheory.K5.ReprSpan
