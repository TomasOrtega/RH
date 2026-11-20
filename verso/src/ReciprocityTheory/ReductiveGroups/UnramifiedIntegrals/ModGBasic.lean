import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) : x ∈ Aio d l ι ↔ ‖ι (x : ℂ)‖ ≤ 1 := by
  rw [Aio, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  try exact Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mem_nonunits_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) :
    x ∈ (Aio d l ι).nonunits ↔ ‖ι (x : ℂ)‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := Aio d l ι)]
  constructor
  · rintro ⟨h1, h2⟩
    have hle : ‖ι (x : ℂ)‖ ≤ 1 := (mem_Aio ι x).1 h1
    refine lt_of_le_of_ne hle fun heq => ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
    apply h2
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at heq
    have hinv : x⁻¹ ∈ Aio d l ι :=
      (mem_Aio ι x⁻¹).2 (le_of_eq (by rw [IntermediateField.coe_inv, map_inv₀, norm_inv, heq, inv_one]))
    have hm : (⟨x, h1⟩ : Aio d l ι) * ⟨x⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩
  · intro h
    refine ⟨(mem_Aio ι x).2 h.le, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have hy := (mem_Aio ι (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d)).1 ((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι).2
    have h0 : ((u : Aio d l ι) : Om d) * (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h0
    have hmul : (x : ℂ) * ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ) = 1 :=
      congrArg (fun t : Om d => (t : ℂ)) h0
    have hn : ‖ι (x : ℂ)‖ * ‖ι ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ)‖ = 1 := by
      simpa using congrArg (fun t => ‖ι t‖) hmul
    nlinarith [norm_nonneg (ι (x : ℂ)), mul_le_mul_of_nonneg_left hy (norm_nonneg (ι (x : ℂ)))]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem inertiaEl_iff {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) :
    InertiaEl A g ↔ g ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype := by
  constructor
  · rintro ⟨hd, hx⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hd⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    refine RingEquiv.ext fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ((⟨g, hd⟩ : A.decompositionSubgroup E) • a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a
    rw [Ideal.Quotient.eq]
    obtain ⟨h1, h2⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).1 (hx a a.2)
    exact h2
  · intro hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨g'.2, fun x hx => ?_⟩
    have key : (g' • (⟨x, hx⟩ : A)) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal A := by
      rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hg'
      have h3 := congrArg (fun f : RingAut (IsLocalRing.ResidueField A) =>
        f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ⟨x, hx⟩)) hg'
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (g' • (⟨x, hx⟩ : A)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) ⟨x, hx⟩ at h3
      exact Ideal.Quotient.eq.1 h3
    have e : ((A.decompositionSubgroup E).subtype g') x - x =
        ((g' • (⟨x, hx⟩ : A) - (⟨x, hx⟩ : A) : A) : Ω) := rfl
    rw [e, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)]
    exact ⟨(g' • (⟨x, hx⟩ : A) - (⟨x, hx⟩ : A)).2, key⟩

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem inertiaEl_mem_hilbert {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {g : Ω ≃ₐ[E] Ω} (h : InertiaEl A g) : g ∈ hilbertSubgroup E Ω := by
  unfold hilbertSubgroup
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure (Or.inl (Or.inr ⟨A, (inertiaEl_iff A g).1 h⟩)))

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h2 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_Om (d : ℕ) {z : ℂ} (hz : IsIntegral ℤ z) : ∃ x : Om d, (x : ℂ) = z ∧ IsIntegral ℤ x := by
  have hzK : IsIntegral (KQ d) z := hz.tower_top
  have hmem : z ∈ Om d := hzK
  refine ⟨⟨z, hmem⟩, rfl, ?_⟩
  exact (isIntegral_algHom_iff (x := (⟨z, hmem⟩ : Om d)) (algebraMap (Om d) ℂ).toIntAlgHom
    (algebraMap (Om d) ℂ).injective).mp hz

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem Om_isAlgebraic (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by
  have hx : IsIntegral (KQ d) (x : ℂ) := x.2
  exact (isIntegral_trans (R := ℚ) _ hx).isAlgebraic

end ReciprocityTheory.ChartRestriction.L1
