import Mathlib

namespace GlobalTheory

open Module

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finset_functions_recovered_from_values {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ))
    (hF : ∀ u ∈ F, u ∈ V) :
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  classical
  set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F
  have hWV : W ≤ V := Submodule.span_le.mpr (fun u hu => hF u hu)
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef
  have hcoan : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : X → ℂ) = 0 := by
      funext x
      have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [← this, hcoan, Submodule.dualAnnihilator_bot]
  let b := Module.finBasis ℂ W
  have hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i := by
    intro i
    have : b.coord i ∈ S := by rw [hS]; trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp this
  choose μ hμ using hμ
  set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef
  have hsub : ∀ i, (μ i).support ⊆ s := fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  refine ⟨s,
    fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))
  · intro u hu
    let w : W := ⟨u, Submodule.subset_span hu⟩
    have hw : (w : X → ℂ) = u := rfl
    have hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x := by
      intro i
      have h1 : b.repr w i = b.coord i w := rfl
      rw [h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]
      · simp [LinearMap.sum_apply, hev, hw]
      · intro x _; simp
    calc u = ((∑ i, b.repr w i • b i : W) : X → ℂ) := by rw [b.sum_repr w]
      _ = ∑ i, b.repr w i • ((b i : W) : X → ℂ) := by
          rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      _ = _ := by
        simp_rw [hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [mul_comm]

end GlobalTheory
