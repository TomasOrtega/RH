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
Introduce `n ε V _ _ E hG L hK hL`. Use `set S := Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS`. Establish `gen : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x ∈ S` using `fun l hl x hx => Submodule.subset_span ⟨l, hl, x, hx, rfl⟩`. Establish `pre : ∀ c d, ε c = true → ε d = false → ∀ y ∈ S, E c d y ∈ S`. Introduce `c d hc hd y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨l, hl, x, hx, rfl⟩` from `hz`. Establish `h1` using `gen ((c, d) :: l) (by`. Introduce `p hp`.

Break down `List.mem_cons.1 hp with rfl | hp` into its components or cases. Conclude with `⟨hc, hd⟩`. Conclude with `hl p hp) x hx`. Simplify `h1` using `only [List.map_cons, List.prod_cons, Module.End.mul_apply]`. Consider the case `zero => rw [map_zero]`.

Conclude with `S.zero_mem`. Consider the case `add u v _ _ hu hv => rw [map_add]`. Conclude with `S.add_mem hu hv`. Consider the case `smul r u _ hu => rw [map_smul]`. Conclude with `S.smul_mem r hu`.

Establish `main : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L, ∀ a b, E a b ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x) ∈ S`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_ x hx a b`.

Simplify using `only [List.map_nil, List.prod_nil, Module.End.one_apply]`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b`. Establish `h1` using `gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)`. Simplify `h1` using `only [List.map_nil, List.prod_nil, Module.End.one_apply]`. Rewrite using `[hL b a hb ha x hx]`.

Conclude with `S.zero_mem`. Establish `h1` using `gen [(a, b)] (by simp [ha, hb]) x hx`. Simplify `h1` using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]`. Establish `h1` using `gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)`. Simplify `h1` using `only [List.map_nil, List.prod_nil, Module.End.one_apply]`.

Consider the case `cons q l ih`. Take `⟨c, d⟩` from `q`. Introduce `hl x hx a b`. Establish `hl' : ∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false` using `fun p hp => hl p (List.mem_cons_of_mem _ hp)`. Establish `hcd : ε c = true ∧ ε d = false` using `hl (c, d) (by simp)`.

Establish `ih'` using `ih hl' x hx`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply]`. Use `set z := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x`. Establish `key : E a b (E c d z) = E c d (E a b z) + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) z`. Rewrite using `[← hG a b c d, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]`.

Normalize the expressions using the abelian group laws. Rewrite using `[key, LinearMap.sub_apply]`. Use `S.add_mem (pre c d hcd.1 hcd.2 _ (ih' a b)) (S.sub_mem ?_ ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `ih' a d`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `S.zero_mem`. Use `split_ifs`. Conclude with `ih' c b`. Rewrite using `[LinearMap.zero_apply]`.

Conclude with `S.zero_mem`. Introduce `a b y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨l, hl, x, hx, rfl⟩` from `hz`.

Conclude with `main l hl x hx a b`. Consider the case `zero => rw [map_zero]`. Conclude with `S.zero_mem`. Consider the case `add u v _ _ hu hv => rw [map_add]`. Conclude with `S.add_mem hu hv`.

Consider the case `smul r u _ hu => rw [map_smul]`. Conclude with `S.smul_mem r hu`.
-/
theorem GlobalTheory.HolDS.raisingSpan_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  intro n ε V _ _ E hG L hK hL
  set S := Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have gen : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x ∈ S :=
    fun l hl x hx => Submodule.subset_span ⟨l, hl, x, hx, rfl⟩
  have pre : ∀ c d, ε c = true → ε d = false → ∀ y ∈ S, E c d y ∈ S := by
    intro c d hc hd y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hz
      have h1 := gen ((c, d) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hc, hd⟩
        · exact hl p hp) x hx
      simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
    | zero => rw [map_zero]; exact S.zero_mem
    | add u v _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
  have main : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      ∀ a b, E a b ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x) ∈ S := by
    intro l
    induction l with
    | nil =>
      intro _ x hx a b
      simp only [List.map_nil, List.prod_nil, Module.End.one_apply]
      cases ha : ε a <;> cases hb : ε b
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
      · rw [hL b a hb ha x hx]; exact S.zero_mem
      · have h1 := gen [(a, b)] (by simp [ha, hb]) x hx
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h1
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
    | cons q l ih =>
      obtain ⟨c, d⟩ := q
      intro hl x hx a b
      have hl' : ∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false := fun p hp => hl p (List.mem_cons_of_mem _ hp)
      have hcd : ε c = true ∧ ε d = false := hl (c, d) (by simp)
      have ih' := ih hl' x hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      set z := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x
      have key : E a b (E c d z) = E c d (E a b z) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) z := by
        rw [← hG a b c d, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [key, LinearMap.sub_apply]
      refine S.add_mem (pre c d hcd.1 hcd.2 _ (ih' a b)) (S.sub_mem ?_ ?_)
      · split_ifs
        · exact ih' a d
        · rw [LinearMap.zero_apply]; exact S.zero_mem
      · split_ifs
        · exact ih' c b
        · rw [LinearMap.zero_apply]; exact S.zero_mem
  intro a b y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, x, hx, rfl⟩ := hz
    exact main l hl x hx a b
  | zero => rw [map_zero]; exact S.zero_mem
  | add u v _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
  | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
