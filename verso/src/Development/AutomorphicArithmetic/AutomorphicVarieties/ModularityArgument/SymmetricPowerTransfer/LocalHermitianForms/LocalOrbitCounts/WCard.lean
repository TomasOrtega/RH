import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.wCard :
    ∀ (T Y : Type) [CommGroup T] [MulAction T Y] (C : Subgroup T) (P F : Set Y), (∀ (t : T) y, y ∈ P → t • y ∈ P) → F ⊆ P → F.Finite →
    (∀ c ∈ C, ∀ y ∈ F, c • y ∈ F) → (∀ y ∈ P, ∃ t : T, t • y ∈ F) → (∀ (t : T), ∀ y ∈ F, t • y ∈ F → ∃ c ∈ C, c • y = t • y) →
    wcount C (P.indicator fun _ => (1 : ℂ)) = (F.ncard : ℂ) := by
  intro T Y _ _ C P F hP hFP hF hCF hPF hU
  classical
  let q : Y → MulAction.orbitRel.Quotient T Y := fun y => Quotient.mk _ y
  have hq : ∀ a b : Y, q a = q b ↔ a ∈ MulAction.orbit T b := by
    intro a b
    rw [← MulAction.orbitRel_apply]
    exact Quotient.eq
  have hstab : ∀ (t : T) (y : Y), MulAction.stabilizer T (t • y) = MulAction.stabilizer T y := by
    intro t y
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (MulAction.injective t).eq_iff
  have hstab' : ∀ a b : Y, a ∈ MulAction.orbit T b →
      MulAction.stabilizer T a = MulAction.stabilizer T b := by
    rintro a b ⟨s, rfl⟩
    exact hstab s b
  have hrel : ∀ z : Y, (MulAction.stabilizer T z).relIndex C = (MulAction.orbit C z).ncard := by
    intro z
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
  have hfib : ∀ z ∈ F, {y | y ∈ F ∧ q y = q z} = MulAction.orbit C z := by
    intro z hz
    ext y
    constructor
    · rintro ⟨hy, hyq⟩
      obtain ⟨s, rfl⟩ := (hq _ _).1 hyq
      obtain ⟨c, hc, hcs⟩ := hU s z hz hy
      exact ⟨⟨c, hc⟩, hcs⟩
    · rintro ⟨c, rfl⟩
      refine ⟨hCF c c.2 z hz, ?_⟩
      exact (hq _ _).2 ⟨(c : T), rfl⟩
  have hsupp : (Function.support fun o : MulAction.orbitRel.Quotient T Y =>
      ((MulAction.stabilizer T (Quotient.out o)).relIndex C : ℂ) *
        P.indicator (fun _ => (1 : ℂ)) (Quotient.out o)) ⊆ ↑(hF.toFinset.image q) := by
    intro o ho
    have hmem : Quotient.out o ∈ P := by
      by_contra h
      exact ho (by simp [Set.indicator_of_notMem h])
    obtain ⟨t, ht⟩ := hPF _ hmem
    simp only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    refine ⟨t • Quotient.out o, ht, ?_⟩
    change q (t • Quotient.out o) = o
    conv_rhs => rw [← Quotient.out_eq o]
    exact (hq _ _).2 ⟨t, rfl⟩
  unfold wcount
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_congr rfl (g := fun o => (({y ∈ hF.toFinset | q y = o}).card : ℂ))]
  · rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Set.ncard_eq_toFinset_card _ hF]
  · intro o ho
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ho
    rw [Set.Finite.mem_toFinset] at hz
    have hzo : Quotient.out (q z) ∈ MulAction.orbit T z := (hq _ _).1 (Quotient.out_eq _)
    have hP' : Quotient.out (q z) ∈ P := by
      obtain ⟨s, hs⟩ := hzo
      rw [← hs]
      exact hP s z (hFP hz)
    rw [Set.indicator_of_mem hP', mul_one, hstab' _ _ hzo, hrel z, ← hfib z hz]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp
