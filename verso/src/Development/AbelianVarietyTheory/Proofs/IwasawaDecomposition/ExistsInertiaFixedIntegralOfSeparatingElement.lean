import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalAlgClosureExistsPosPowApplyEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `e : a = 1 - (1 - a)` using `by ring`. Rewrite using `[e]`. Use `le_trans (Valuation.map_sub _ _ _) (max_le ?_ ha.le)` and prove the remaining obligations. Rewrite using `[map_one]`.
-/
theorem valuation_le_one_of_valuation_one_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {a : Ω} (ha : A.valuation (1 - a) < 1) : A.valuation a ≤ 1 := by
  have e : a = 1 - (1 - a) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ha.le)
  rw [map_one]

/- English proof (translation)
Establish `e : 1 - a * b = (1 - a) + a * (1 - b)` using `by ring`. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ha ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_one_sub_mul_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation (1 - a) < 1) (hb : A.valuation (1 - b) < 1) :
    A.valuation (1 - a * b) < 1 := by
  have e : 1 - a * b = (1 - a) + a * (1 - b) := by ring
  rw [e]
  refine Valuation.map_add_lt _ ha ?_
  rw [map_mul]
  calc A.valuation a * A.valuation (1 - b) ≤ 1 * A.valuation (1 - b) :=
        by gcongr; exact valuation_le_one_of_valuation_one_sub_lt A ha
    _ = A.valuation (1 - b) := one_mul _
    _ < 1 := hb

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A A' σ hσ e₀ c hint hA hA'`. Take `⟨k, hk, hfix⟩` from `galAlgClosure_exists_pos_pow_apply_eq E Ω σ e₀`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use `set f : ℕ → Ω := fun i => (σ ^ i) e₀ with hf`. Establish `hfint : ∀ i, IsIntegral ℤ (f i)` using `fun i => hint.map ((σ ^ i : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom.toIntAlgHom)`.

Establish `hshift : ∀ i, σ (f i) = f (i + 1)`. Introduce `i`. Simplify using `only [hf, pow_succ', AlgEquiv.mul_apply]`. Establish `hcong : ∀ i, A'.valuation (1 - f i) < 1`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simpa [hf] using hA'`. Consider the case `succ i ih`. Establish `hy : A'.valuation (f i) ≤ 1` using `valuation_le_one_of_valuation_one_sub_lt A' ih`. Establish `hmove` using `hσ.2 (f i) hy`.

Establish `e : 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i)`. Rewrite using `[← hshift i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ih ?_` and prove the remaining obligations.

Rewrite using `[Valuation.map_neg]`. Conclude with `hmove`. Use `⟨∏ i ∈ Finset.range (m + 1), f i, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsIntegral.prod _ (fun i _ => hfint i)`. Rewrite using `[map_prod]`.

Simplify using `only [hshift]`. Rewrite using `[Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]`. Establish `h0 : f (m + 1) = f 0` using `by simpa [hf] using hfix`. Rewrite using `[h0]`. Rewrite using `[Finset.prod_range_succ']`.

Establish `hP : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1))` using `IsIntegral.prod _ (fun i _ => hfint (i + 1))`. Establish `hPle : A.valuation (∏ i ∈ Finset.range m, f (i + 1)) ≤ 1` using `(A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hP)`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_induction f (fun x => A'.valuation (1 - x) < 1) (fun a b ha hb => valuation_one_sub_mul_lt A' ha hb) ?_ (fun i _ => hcong i)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem exists_fixed_of_separating :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' σ hσ e₀ c hint hA hA'
  obtain ⟨k, hk, hfix⟩ := galAlgClosure_exists_pos_pow_apply_eq E Ω σ e₀
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set f : ℕ → Ω := fun i => (σ ^ i) e₀ with hf
  have hfint : ∀ i, IsIntegral ℤ (f i) := fun i =>
    hint.map ((σ ^ i : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom.toIntAlgHom)
  have hshift : ∀ i, σ (f i) = f (i + 1) := by
    intro i
    simp only [hf, pow_succ', AlgEquiv.mul_apply]

  have hcong : ∀ i, A'.valuation (1 - f i) < 1 := by
    intro i
    induction i with
    | zero => simpa [hf] using hA'
    | succ i ih =>
      have hy : A'.valuation (f i) ≤ 1 := valuation_le_one_of_valuation_one_sub_lt A' ih
      have hmove := hσ.2 (f i) hy
      have e : 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i) := by
        rw [← hshift i]; ring
      rw [e]
      refine Valuation.map_add_lt _ ih ?_
      rw [Valuation.map_neg]
      exact hmove
  refine ⟨∏ i ∈ Finset.range (m + 1), f i, ?_, ?_, ?_, ?_⟩
  · exact IsIntegral.prod _ (fun i _ => hfint i)
  · rw [map_prod]
    simp only [hshift]
    rw [Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]
    have h0 : f (m + 1) = f 0 := by simpa [hf] using hfix
    rw [h0]
  · rw [Finset.prod_range_succ']
    have hP : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1)) :=
      IsIntegral.prod _ (fun i _ => hfint (i + 1))
    have hPle : A.valuation (∏ i ∈ Finset.range m, f (i + 1)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hP)
    rw [map_mul]
    calc A.valuation (∏ i ∈ Finset.range m, f (i + 1)) * A.valuation (f 0)
        ≤ 1 * A.valuation (f 0) := by gcongr
      _ = A.valuation e₀ := by simp [hf]
      _ < A.valuation c := hA
  · refine Finset.prod_induction f (fun x => A'.valuation (1 - x) < 1)
      (fun a b ha hb => valuation_one_sub_mul_lt A' ha hb) ?_ (fun i _ => hcong i)
    simp

end GlobalTheory
