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
Introduce `n ε V _ _ E hG w c d hcd hεcd hw s t l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_`. Simplify using `only [List.map_nil, List.prod_nil, Module.End.one_apply, hw]`.

Conclude with `Submodule.zero_mem _`. Consider the case `cons p l ih`. Take `⟨a, b⟩` from `p`. Introduce `hl`. Establish `hab : ε a = s ∧ ε b = t` using `hl (a, b) List.mem_cons_self`.

Establish `hl' : ∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t` using `fun p hp => hl p (List.mem_cons_of_mem _ hp)`. Establish `IH` using `ih hl'`. Establish `hcd' : (c : ℕ) < (d : ℕ)` using `hcd`. Use `set y := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w with hy`. Establish `hword : ((( (a, b) :: l).map fun p : Fin n × Fin n => E p.1 p.2).prod w) = E a b y`.

Simplify using `[hy, Module.End.mul_apply]`. Rewrite using `[hword]`. Establish `key : E c d (E a b y) = E a b (E c d y) + ((if d = a then E c b else 0) - (if b = c then E a d else 0)) y`. Establish `h` using `congrArg (fun f : Module.End ℂ V => f y) (hG c d a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`.

Rewrite using `[LinearMap.sub_apply, ← h]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `hm : E a b (E c d y) ∈ (Submodule.span ℂ _).map (E a b)` using `Submodule.mem_map_of_mem IH`.

Rewrite `hm` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨z, ⟨l', hlen, hty, hh, rfl⟩, rfl⟩`. Use `⟨(a, b) :: l', by simp [hlen], ?_, ?_, by simp [Module.End.mul_apply]⟩` and prove the remaining obligations. Introduce `p hp`.

Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Use `exacts [hab, hty p hp]`. Simplify using `only [List.map_cons, List.sum_cons]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[LinearMap.sub_apply]`.

Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Use `split_ifs with h1`. Substitute `h1` using the available equality. Use `Submodule.subset_span ⟨(c, b) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩` and prove the remaining obligations. Introduce `p hp`.

Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Use `exacts [⟨hεcd.trans hab.1, hab.2⟩, hl' p hp]`. Simplify using `only [List.map_cons, List.sum_cons]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [LinearMap.zero_apply]`.

Conclude with `Submodule.zero_mem _`. Use `split_ifs with h2`. Substitute `h2` using the available equality. Use `Submodule.subset_span ⟨(a, d) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩` and prove the remaining obligations. Introduce `p hp`.

Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Use `exacts [⟨hab.1, hεcd.symm.trans hab.2⟩, hl' p hp]`. Simplify using `only [List.map_cons, List.sum_cons]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [LinearMap.zero_apply]`.

Conclude with `Submodule.zero_mem _`.
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
