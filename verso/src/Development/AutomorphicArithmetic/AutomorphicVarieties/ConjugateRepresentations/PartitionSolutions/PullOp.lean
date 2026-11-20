import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open scoped ContDiff

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hC l hl`. Establish `hY : IsOpen G.Y` using `G.isOpen`. Establish `hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y` using `fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp`. Establish `hw : ∀ q (w : G.Om q) (s : S), ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧ ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0` using `fun q w => w.2`. Establish `mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q`.

Introduce `q w s`. Use `⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩` and prove the remaining obligations. Conclude with `(pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr fun p hp => Set.indicator_of_mem hp _`. Establish `padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V), pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p`. Introduce `q s a b p`.

Use extensionality with `v`. Simplify using `[pull]`. Establish `psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V), pull (l s) (c • a) p = c • pull (l s) a p`. Introduce `q s c a p`. Use extensionality with `v`.

Simplify using `[pull]`. Establish `ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y → extDeriv (G.Y.indicator om) p = extDeriv om p`. Introduce `q om p hp`. Simplify using `only [extDeriv]`. Rewrite using `[Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]`.

Set `P : ∀ q, G.Om q →ₗ[ℂ] G.Om q` to `fun q => { toFun := fun w => ⟨_, mem q w⟩ map_add' := by`. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Simplify using `only [Submodule.coe_add, Pi.add_apply]`.

Distinguish the cases in `hp : p ∈ G.Y`. Simplify using `only [Set.indicator_of_mem hp]`. Conclude with `padd q s _ _ p`. Simplify using `[Set.indicator, hp]`. Use the proof step `map_smul' := by`.

Introduce `c a`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]`. Distinguish the cases in `hp : p ∈ G.Y`.

Simplify using `only [Set.indicator_of_mem hp]`. Conclude with `psmul q s c _ p`. Simplify using `[Set.indicator, hp] }`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q w s p hp`.

Conclude with `Set.indicator_of_mem hp _`. Introduce `q w`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Distinguish the cases in `hp : p ∈ G.Y`.

Rewrite using `[Geo.dOm_apply G _ s hp]`. Express the relevant statement in the definitionally equal form `extDeriv (G.Y.indicator _) p = G.Y.indicator _ p`. Rewrite using `[ext_ind _ _ _ hp, Set.indicator_of_mem hp, (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]`. Simplify using `only [pull]`. Rewrite using `[Geo.dOm_apply G w s (hpos s p hp)]`.

Conclude with `((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm`. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Distinguish the cases in `hp : p ∈ G.Y`.

Express the relevant statement in the definitionally equal form `G.Y.indicator _ p = _`. Rewrite using `[Set.indicator_of_mem hp]`. Use extensionality with `v`. Simplify using `only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]`. Rewrite using `[Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]`.

Conclude with `((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm`.
-/
theorem UpperTheory.V.Cj.A.pullOp :
    PullOp := by
  intro Γ V S _ _ _ _ d G hC l hl
  have hY : IsOpen G.Y := G.isOpen
  have hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y := fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp
  have hw : ∀ q (w : G.Om q) (s : S),
      ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := fun q w => w.2
  have mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator
      (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q := by
    intro q w s
    refine ⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩
    exact (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr
      fun p hp => Set.indicator_of_mem hp _
  have padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p := by
    intro q s a b p
    ext v
    simp [pull]
  have psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (c • a) p = c • pull (l s) a p := by
    intro q s c a p
    ext v
    simp [pull]
  have ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y →
      extDeriv (G.Y.indicator om) p = extDeriv om p := by
    intro q om p hp
    simp only [extDeriv]
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]
  let P : ∀ q, G.Om q →ₗ[ℂ] G.Om q := fun q =>
    { toFun := fun w => ⟨_, mem q w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_add, Pi.add_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact padd q s _ _ p
        · simp [Set.indicator, hp]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact psmul q s c _ p
        · simp [Set.indicator, hp] }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro q w s p hp
    exact Set.indicator_of_mem hp _
  · intro q w
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · rw [Geo.dOm_apply G _ s hp]
      change extDeriv (G.Y.indicator _) p = G.Y.indicator _ p
      rw [ext_ind _ _ _ hp, Set.indicator_of_mem hp,
        (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]
      simp only [pull]
      rw [Geo.dOm_apply G w s (hpos s p hp)]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
  · intro f
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · change G.Y.indicator _ p = _
      rw [Set.indicator_of_mem hp]
      ext v
      simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
