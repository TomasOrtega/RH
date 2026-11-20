import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetFn
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Simplify using `only [deltaR, nabs, map_mul, NNReal.coe_mul, mul_zpow]`.
-/
theorem deltaR_mul (g g' : GL n k) : deltaR c (g * g') = deltaR c g * deltaR c g' := by
  simp only [deltaR, nabs, map_mul, NNReal.coe_mul, mul_zpow]

/- English proof (translation)
Simplify using `[deltaR, nabs]`.
-/
theorem deltaR_one : deltaR c (1 : GL n k) = 1 := by
  simp [deltaR, nabs]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)`.
-/
theorem mul_embX_mem_R {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (g : GL n k) :
    u * embX c g ∈ R k n c 1 :=
  mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)

/- English proof (translation)
Establish `h1 : g'⁻¹ * g ∈ prX (Cgrp J h)`. Use `⟨embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹, Radical.conj_mem _ (mul_mem (inv_mem hu') hu), ?_⟩` and prove the remaining obligations. Establish `e2 : embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹ * embX c (g'⁻¹ * g) = (u' * embX c g')⁻¹ * (u * embX c g)`. Simplify using `only [map_mul, map_inv]`. Use `group`.

Rewrite using `[e2]`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mul_embX_mem_R hu' g')) (mul_embX_mem_R hu g), ?_⟩` and prove the remaining obligations. Establish `e3 : u * embX c g = u' * embX c g' * h * j' * j⁻¹ * h⁻¹`. Rewrite using `[← e]`. Use `group`.

Establish `e4 : h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ = j' * j⁻¹`. Rewrite using `[e3]`. Use `group`. Use `show h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ ∈ J`. Rewrite using `[e4]`.

Conclude with `mul_mem hj' (inv_mem hj)`. Establish `h2` using `deltaR_mul (c := c) g' (g'⁻¹ * g)`. Rewrite `h2` using `[H _ h1, mul_inv_cancel_left, mul_one]`. Conclude with `h2`.
-/
theorem deltaR_eq {J : Subgroup (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) {u u' j j' : GL (n ⊕ Fin c) k} {g g' : GL n k}
    (hu : u ∈ N k n c 1) (hu' : u' ∈ N k n c 1) (hj : j ∈ J) (hj' : j' ∈ J)
    (e : u * embX c g * h * j = u' * embX c g' * h * j') : deltaR c g = deltaR c g' := by
  have h1 : g'⁻¹ * g ∈ prX (Cgrp J h) := by
    refine ⟨embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹,
      Radical.conj_mem _ (mul_mem (inv_mem hu') hu), ?_⟩
    have e2 : embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹ * embX c (g'⁻¹ * g)
        = (u' * embX c g')⁻¹ * (u * embX c g) := by
      simp only [map_mul, map_inv]; group
    rw [e2]
    refine Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mul_embX_mem_R hu' g')) (mul_embX_mem_R hu g), ?_⟩
    have e3 : u * embX c g = u' * embX c g' * h * j' * j⁻¹ * h⁻¹ := by
      rw [← e]; group
    have e4 : h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ = j' * j⁻¹ := by
      rw [e3]; group
    show h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ ∈ J
    rw [e4]
    exact mul_mem hj' (inv_mem hj)
  have h2 := deltaR_mul (c := c) g' (g'⁻¹ * g)
  rw [H _ h1, mul_inv_cancel_left, mul_one] at h2
  exact h2

end

/- English proof (translation)
Set `P : GL (n ⊕ Fin c) k → GL n k → Prop` to `fun x g => ∃ u ∈ N k n c 1, ∃ j ∈ J, x = u * embX c g * h * j`. Set `f : GL (n ⊕ Fin c) k → ℂ` to `fun x => if hx : ∃ g, P x g then (deltaR c hx.choose : ℂ) else 0`. Establish `fpos : ∀ x g, P x g → f x = (deltaR c g : ℂ)`. Introduce `x g hg`. Establish `hx : ∃ g, P x g` using `⟨g, hg⟩`.

Take `⟨u, hu, j, hj, e⟩` from `hx.choose_spec`. Take `⟨u', hu', j', hj', e'⟩` from `hg`. Simplify using `only [f, dif_pos hx]`. Rewrite using `[deltaR_eq H hu hu' hj hj' (e.symm.trans e')]`. Establish `fneg : ∀ x, (¬ ∃ g, P x g) → f x = 0` using `fun x hx => by simp only [f, dif_neg hx]`.

Establish `left : ∀ u ∈ N k n c 1, ∀ (g g' : GL n k) x, P x g' → P (u * embX c g * x) (g * g')`. Introduce and unpack `u hu g g' x ⟨u', hu', j, hj, rfl⟩`. Use `⟨u * (embX c g * u' * (embX c g)⁻¹), mul_mem hu (Radical.conj_mem _ hu'), j, hj, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Use `group`.

Establish `right : ∀ j ∈ J, ∀ g x, P x g → P (x * j) g`. Introduce and unpack `j hj g x ⟨u', hu', j', hj', rfl⟩`. Conclude with `⟨u', hu', j' * j, mul_mem hj' hj, by group⟩`. Use `⟨f, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu g x`.

Distinguish the cases in `hx : ∃ g', P x g'`. Take `⟨g', hg'⟩` from `hx`. Rewrite using `[fpos _ _ (left u hu g g' x hg'), fpos _ _ hg', deltaR_mul]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[fneg x hx, mul_zero]`. Apply `fneg` to reduce the goal to its premises. Introduce and unpack `⟨g', hg'⟩`. Apply `hx` to reduce the goal to its premises. Use `left _ (Radical.conj_mem g⁻¹ (inv_mem hu)) g⁻¹ g' _ hg'` as an intermediate fact.

Establish `e : embX c g⁻¹ * u⁻¹ * (embX c g⁻¹)⁻¹ * embX c g⁻¹ * (u * embX c g * x) = x`. Simplify using `only [map_inv]`. Use `group`. Rewrite `this` using `[e]`. Conclude with `⟨_, this⟩`.

Introduce `x j hj`. Distinguish the cases in `hx : ∃ g', P x g'`. Take `⟨g', hg'⟩` from `hx`. Rewrite using `[fpos _ _ (right j hj g' x hg'), fpos _ _ hg']`. Rewrite using `[fneg x hx]`.

Apply `fneg` to reduce the goal to its premises. Introduce and unpack `⟨g', hg'⟩`. Apply `hx` to reduce the goal to its premises. Use `right _ (inv_mem hj) g' _ hg'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`.

Conclude with `⟨_, this⟩`. Introduce `x hx`. Apply `fneg` to reduce the goal to its premises. Introduce and unpack `⟨g, u, hu, j, hj, e⟩`. Apply `hx` to reduce the goal to its premises.

Use `symm`. Rewrite using `[DoubleCoset.eq]`. Conclude with `⟨_, mul_embX_mem_R hu g, j, hj, e⟩`. Rewrite using `[fpos h 1 ⟨1, one_mem _, 1, one_mem _, by simp⟩, deltaR_one]`. Simplify using the standard rewrite rules.
-/
theorem exists_isCosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) : ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  classical
  let P : GL (n ⊕ Fin c) k → GL n k → Prop := fun x g =>
    ∃ u ∈ N k n c 1, ∃ j ∈ J, x = u * embX c g * h * j
  let f : GL (n ⊕ Fin c) k → ℂ := fun x =>
    if hx : ∃ g, P x g then (deltaR c hx.choose : ℂ) else 0
  have fpos : ∀ x g, P x g → f x = (deltaR c g : ℂ) := by
    intro x g hg
    have hx : ∃ g, P x g := ⟨g, hg⟩
    obtain ⟨u, hu, j, hj, e⟩ := hx.choose_spec
    obtain ⟨u', hu', j', hj', e'⟩ := hg
    simp only [f, dif_pos hx]
    rw [deltaR_eq H hu hu' hj hj' (e.symm.trans e')]
  have fneg : ∀ x, (¬ ∃ g, P x g) → f x = 0 := fun x hx => by simp only [f, dif_neg hx]
  have left : ∀ u ∈ N k n c 1, ∀ (g g' : GL n k) x, P x g' → P (u * embX c g * x) (g * g') := by
    rintro u hu g g' x ⟨u', hu', j, hj, rfl⟩
    refine ⟨u * (embX c g * u' * (embX c g)⁻¹), mul_mem hu (Radical.conj_mem _ hu'), j, hj, ?_⟩
    simp only [map_mul]; group
  have right : ∀ j ∈ J, ∀ g x, P x g → P (x * j) g := by
    rintro j hj g x ⟨u', hu', j', hj', rfl⟩
    exact ⟨u', hu', j' * j, mul_mem hj' hj, by group⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu g x
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (left u hu g g' x hg'), fpos _ _ hg', deltaR_mul]
      push_cast; rfl
    · rw [fneg x hx, mul_zero]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := left _ (Radical.conj_mem g⁻¹ (inv_mem hu)) g⁻¹ g' _ hg'
      have e : embX c g⁻¹ * u⁻¹ * (embX c g⁻¹)⁻¹ * embX c g⁻¹ * (u * embX c g * x) = x := by
        simp only [map_inv]; group
      rw [e] at this
      exact ⟨_, this⟩
  · intro x j hj
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (right j hj g' x hg'), fpos _ _ hg']
    · rw [fneg x hx]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := right _ (inv_mem hj) g' _ hg'
      rw [mul_inv_cancel_right] at this
      exact ⟨_, this⟩
  · intro x hx
    apply fneg
    rintro ⟨g, u, hu, j, hj, e⟩
    apply hx
    symm
    rw [DoubleCoset.eq]
    exact ⟨_, mul_embX_mem_R hu g, j, hj, e⟩
  · rw [fpos h 1 ⟨1, one_mem _, 1, one_mem _, by simp⟩, deltaR_one]
    simp

end GlobalTheory.CosetFn
