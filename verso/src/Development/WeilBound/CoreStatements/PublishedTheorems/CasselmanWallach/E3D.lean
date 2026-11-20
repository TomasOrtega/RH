import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS`. Set `Dop : List (Mx n) → (E →L[ℂ] E)` to `fun l => l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)`. Establish `key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v)`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil => intro _ v hv`. Conclude with `⟨hv, rfl⟩`. Consider the case `cons X l ih`. Introduce `hl v hv`. Take `⟨h1, h2⟩` from `ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv`.

Use `⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩` and prove the remaining obligations. Use `show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))`. Rewrite using `[hd X (hl X List.mem_cons_self) _ h1, h2]`. Establish `hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E))` using `fun l => by`. Rewrite using `[Seminorm.coe_comp, ContinuousLinearMap.coe_coe]`.

Conclude with `hq.comp (Dop l).continuous`. Establish `hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w → ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w)`. Introduce `l hl`. Use `(he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `key l hl y hy`.

Combine the equalities or inequalities in the displayed calculation. Establish `main : ∀ S : List (List (Mx n)), Words (lieSet ε) S → ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w)`. Introduce `S`. Proceed by induction on `S with`. Consider the case `nil`.

Introduce `_`. Use `⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩` and prove the remaining obligations. Simplify using `[sobNorm]`. Consider the case `cons l S ih`. Introduce `hS`.

Take `⟨q', hq', h'⟩` from `ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))`. Establish `hl : ∀ X ∈ l, X ∈ lieSet ε` using `hS l List.mem_cons_self`. Use `⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩` and prove the remaining obligations. Rewrite using `[Seminorm.coe_add]`. Conclude with `(hcont l).add hq'`.

Establish `e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w` using `by first`. Consider the case `rfl`. Consider the case `simp [sobNorm]`. Rewrite using `[e, Seminorm.add_apply]`. Conclude with `add_le_add (hw l hl w hw') (h' w hw')`.

Conclude with `main S hS`.
-/
theorem e3d : SobolevNormDomination := by
  intro he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS
  let Dop : List (Mx n) → (E →L[ℂ] E) := fun l =>
    l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)
  have key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v →
      IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v) := by
    intro l
    induction l with
    | nil => intro _ v hv; exact ⟨hv, rfl⟩
    | cons X l ih =>
      intro hl v hv
      obtain ⟨h1, h2⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv
      refine ⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩
      show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))
      rw [hd X (hl X List.mem_cons_self) _ h1, h2]
  have hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E)) := fun l => by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact hq.comp (Dop l).continuous
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w →
      ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w) := by
    intro l hl
    refine (he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_
    obtain ⟨h1, h2⟩ := key l hl y hy
    calc ‖Dw σ l y‖ ≤ q (T (Dw σ l y)) := hq1 _ h1
      _ = _ := by rw [h2]; rfl
  have main : ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w) := by
    intro S
    induction S with
    | nil =>
      intro _
      refine ⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩
      simp [sobNorm]
    | cons l S ih =>
      intro hS
      obtain ⟨q', hq', h'⟩ := ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))
      have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
      refine ⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩
      · rw [Seminorm.coe_add]
        exact (hcont l).add hq'
      · have e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w := by
          first
            | rfl
            | simp [sobNorm]
        rw [e, Seminorm.add_apply]
        exact add_le_add (hw l hl w hw') (h' w hw')
  exact main S hS

end PositivityTheory.CW

end
