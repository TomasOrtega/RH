import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPowStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ`. Establish `hunif : ∀ v : Place k F, ∃ π : F, π ≠ 0 ∧ ord v π = 1` using `fun v => (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.1`. Use `choose π hπ0 hπ1 using hunif`. Establish `hfib : ∀ v, {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E (π v)) = Module.finrank F E` using `fun v => GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k F E hFF ρ hρ v (π v) (hπ0 v) (hπ1 v)`. Establish `hkey : ∀ p x, ord p (algebraMap F E x) = ord p (algebraMap F E (π (ρ p))) * ord (ρ p) x`.

Introduce `p x`. Take `⟨e, -, -, he⟩` from `(GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).2 ρ hρ p`. Rewrite using `[he x, he (π (ρ p)), hπ1, mul_one]`. Establish `hpre : ∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite`. Introduce `s hs`.

Establish `h : ρ ⁻¹' s = ⋃ v ∈ s, {p | ρ p = v}` using `by ext p; simp`. Rewrite using `[h]`. Conclude with `hs.biUnion fun v _ => (hfib v).1`. Use `⟨hpre, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `hT` using `hpre _ hφ`.

Establish `hsupp : (Function.support fun p => ord p (algebraMap F E (φ (ρ p)))) ⊆ ↑hT.toFinset`. Introduce `p hp`. Simplify using `only [Function.mem_support] at hp`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_setOf_eq]`. Introduce `h`.

Apply `hp` to reduce the goal to its premises. Rewrite using `[hkey, h, mul_zero]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by intro v hv; simpa using hv)]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := hφ.toFinset) (by intro p hp; simpa using hp)]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hc : ∀ p ∈ hT.toFinset.filter (fun p => ρ p = v), ord p (algebraMap F E (φ (ρ p))) = ord p (algebraMap F E (π v)) * ord v (φ v)`. Introduce `p hp`. Establish `hpv` using `(Finset.mem_filter.1 hp).2`.

Rewrite using `[hkey, hpv]`. Rewrite using `[Finset.sum_congr rfl hc, ← Finset.sum_mul]`. Use `congr 1`. Rewrite using `[← (hfib v).2, finsum_mem_eq_finite_toFinset_sum _ (hfib v).1]`. Use `congr 1`.

Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`.

Introduce `h`. Conclude with `⟨h ▸ hv, h⟩`.
-/
theorem finsum_ord_pull_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ
  classical
  have hunif : ∀ v : Place k F, ∃ π : F, π ≠ 0 ∧ ord v π = 1 := fun v => (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.1
  choose π hπ0 hπ1 using hunif
  have hfib : ∀ v, {p | ρ p = v}.Finite ∧
      ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E (π v)) = Module.finrank F E :=
    fun v => GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k F E hFF ρ hρ v (π v) (hπ0 v) (hπ1 v)
  have hkey : ∀ p x, ord p (algebraMap F E x) = ord p (algebraMap F E (π (ρ p))) * ord (ρ p) x := by
    intro p x
    obtain ⟨e, -, -, he⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).2 ρ hρ p
    rw [he x, he (π (ρ p)), hπ1, mul_one]
  have hpre : ∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite := by
    intro s hs
    have h : ρ ⁻¹' s = ⋃ v ∈ s, {p | ρ p = v} := by ext p; simp
    rw [h]; exact hs.biUnion fun v _ => (hfib v).1
  refine ⟨hpre, fun φ hφ => ?_⟩
  have hT := hpre _ hφ
  have hsupp : (Function.support fun p => ord p (algebraMap F E (φ (ρ p)))) ⊆ ↑hT.toFinset := by
    intro p hp
    simp only [Function.mem_support] at hp
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
    intro h; apply hp; rw [hkey, h, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [finsum_eq_sum_of_support_subset _ (s := hφ.toFinset) (by intro v hv; simpa using hv)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := hφ.toFinset) (by intro p hp; simpa using hp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hc : ∀ p ∈ hT.toFinset.filter (fun p => ρ p = v),
      ord p (algebraMap F E (φ (ρ p))) = ord p (algebraMap F E (π v)) * ord v (φ v) := by
    intro p hp
    have hpv := (Finset.mem_filter.1 hp).2
    rw [hkey, hpv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
  congr 1
  rw [← (hfib v).2, finsum_mem_eq_finite_toFinset_sum _ (hfib v).1]
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hv, h⟩

end GlobalTheory.Nef
