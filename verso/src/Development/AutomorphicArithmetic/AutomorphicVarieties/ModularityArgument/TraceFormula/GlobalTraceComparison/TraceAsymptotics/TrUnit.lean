import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← QuotientGroup.out_eq' q]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Simplify using `using h`.

Introduce `h`. Establish `h1 : (QuotientGroup.mk q.out : G ⧸ K) = QuotientGroup.mk 1`. Rewrite using `[QuotientGroup.out_eq' q, h]`. Establish `h2` using `QuotientGroup.eq.1 h1`. Simplify using `using h2`.
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
Establish `hone : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K` using `(out_mem_iff K _).2 rfl`. Unfold `levOp`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)]`. Rewrite using `[Set.indicator_of_mem (by exact hone)]`. Simplify using the standard rewrite rules.

Introduce `q hq`. Rewrite using `[Set.indicator_of_notMem (fun h => hq ((out_mem_iff K q).1 h)), zero_smul]`.
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
Establish `hone : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K` using `(out_mem_iff K _).2 rfl`. Rewrite using `[levOp_unit_eq]`. Simplify using `using hv ⟨_, hone⟩`.
-/
private theorem levOp_unit_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    levOp ρ K K ((K : Set G).indicator 1) LinearMap.id v = v := by
  have hone : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (out_mem_iff K _).2 rfl
  rw [levOp_unit_eq]
  simpa using hv ⟨_, hone⟩

/- English proof (translation)
Introduce `G V _ _ _ ρ K`. Establish `h : ∀ v ∈ fixed ρ K, levOp ρ K K ((K : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K`. Introduce `v hv`. Rewrite using `[levOp_unit_fixed ρ K v hv]`. Conclude with `hv`.

Establish `hid : (levOp ρ K K ((K : Set G).indicator 1) LinearMap.id).restrict h = LinearMap.id`. Use extensionality with `v`. Simplify using `[LinearMap.restrict_apply, levOp_unit_fixed ρ K v.1 v.2]`. Unfold `twTr`. Rewrite using `[dif_pos h, hid]`.

Distinguish the cases in `hf : FiniteDimensional ℂ (fixed ρ K)`. Conclude with `LinearMap.trace_id ℂ _`. Rewrite using `[Module.finrank_of_not_finite hf, Nat.cast_zero]`. Unfold `LinearMap.trace`. Rewrite using `[dif_neg]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨s, ⟨b⟩⟩`. Conclude with `hf (Module.Finite.of_basis b)`.
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
