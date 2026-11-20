import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem out_mem_iff {G : Type} [Group G] (K : Subgroup G) (q : G ⧸ K) :
    q.out ∈ K ↔ q = (QuotientGroup.mk 1 : G ⧸ K) := by
  constructor
  · intro h
    rw [← QuotientGroup.out_eq' q]
    refine QuotientGroup.eq.2 ?_
    simpa using h
  · intro h
    have h1 : (QuotientGroup.mk q.out : G ⧸ K) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.out_eq' q, h]
    have h2 := QuotientGroup.eq.1 h1
    simpa using h2

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
private theorem levOp_unit_eq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    levOp ρ K K ((K : Set G).indicator 1) LinearMap.id = ρ (QuotientGroup.mk 1 : G ⧸ K).out := by
  have hone : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (out_mem_iff K _).2 rfl
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)]
  · rw [Set.indicator_of_mem (by exact hone)]
    simp
  · intro q hq
    rw [Set.indicator_of_notMem (fun h => hq ((out_mem_iff K q).1 h)), zero_smul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem levOp_unit_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    levOp ρ K K ((K : Set G).indicator 1) LinearMap.id v = v := by
  have hone : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (out_mem_iff K _).2 rfl
  rw [levOp_unit_eq]
  simpa using hv ⟨_, hone⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem trUnit : TrUnit := by
  intro G V _ _ _ ρ K
  have h : ∀ v ∈ fixed ρ K, levOp ρ K K ((K : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K := by
    intro v hv
    rw [levOp_unit_fixed ρ K v hv]
    exact hv
  have hid : (levOp ρ K K ((K : Set G).indicator 1) LinearMap.id).restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_unit_fixed ρ K v.1 v.2]
  unfold twTr
  rw [dif_pos h, hid]
  by_cases hf : FiniteDimensional ℂ (fixed ρ K)
  · exact LinearMap.trace_id ℂ _
  · rw [Module.finrank_of_not_finite hf, Nat.cast_zero]
    unfold LinearMap.trace
    rw [dif_neg]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Finite.of_basis b)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
