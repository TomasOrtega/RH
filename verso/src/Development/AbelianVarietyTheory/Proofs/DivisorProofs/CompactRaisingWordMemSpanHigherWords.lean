import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem GlobalTheory.HolDS.compactRaise_word_higher : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (w : V) (c d : Fin n), c < d → ε c = ε d → E c d w = 0 → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → E c d ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) ∈ Submodule.span ℂ {y : V | ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum < (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧ y = (l'.map fun p : Fin n × Fin n => E p.1 p.2).prod w} := by
  intro n ε V _ _ E hG w c d hcd hεcd hw s t l
  induction l with
  | nil =>
    intro _
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply, hw]
    exact Submodule.zero_mem _
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    intro hl
    have hab : ε a = s ∧ ε b = t := hl (a, b) List.mem_cons_self
    have hl' : ∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have IH := ih hl'
    have hcd' : (c : ℕ) < (d : ℕ) := hcd
    set y := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w with hy
    have hword : ((( (a, b) :: l).map fun p : Fin n × Fin n => E p.1 p.2).prod w) = E a b y := by
      simp [hy, Module.End.mul_apply]
    rw [hword]
    have key : E c d (E a b y) = E a b (E c d y) +
        ((if d = a then E c b else 0) - (if b = c then E a d else 0)) y := by
      have h := congrArg (fun f : Module.End ℂ V => f y) (hG c d a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [LinearMap.sub_apply, ← h]; abel
    rw [key]
    refine Submodule.add_mem _ ?_ ?_
    · have hm : E a b (E c d y) ∈ (Submodule.span ℂ _).map (E a b) := Submodule.mem_map_of_mem IH
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨z, ⟨l', hlen, hty, hh, rfl⟩, rfl⟩
      refine ⟨(a, b) :: l', by simp [hlen], ?_, ?_, by simp [Module.End.mul_apply]⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        exacts [hab, hty p hp]
      · simp only [List.map_cons, List.sum_cons]; linarith
    · rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with h1
        · subst h1
          refine Submodule.subset_span ⟨(c, b) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hεcd.trans hab.1, hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
      · split_ifs with h2
        · subst h2
          refine Submodule.subset_span ⟨(a, d) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hab.1, hεcd.symm.trans hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
