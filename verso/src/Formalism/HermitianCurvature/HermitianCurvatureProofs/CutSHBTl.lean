import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ k r z z' π π' X L hX S _ _ l w a b`. Use `set Qa : Subalgebra ℂ (Module.End ℂ (RadSp k r z z' π π')) := Algebra.adjoin ℂ (Set.range (X.op l)) with hQa`. Set `good : Pr (RadSp k r z z' π π') → Prop` to `fun x => x.1 ∈ Qa ∧ x.2.unop ∈ Qa`. Establish `hop : ∀ i, X.op l i ∈ Qa` using `fun i => Algebra.subset_adjoin ⟨i, rfl⟩`. Establish `gmul : ∀ x y, good x → good y → good (x * y)` using `fun x y hx hy => ⟨Subalgebra.mul_mem _ hx.1 hy.1, Subalgebra.mul_mem _ hy.2 hx.2⟩`.

Establish `gadd : ∀ x y, good x → good y → good (x + y)` using `fun x y hx hy => ⟨Subalgebra.add_mem _ hx.1 hy.1, Subalgebra.add_mem _ hx.2 hy.2⟩`. Establish `gneg : ∀ x, good x → good (-x)` using `fun x hx => ⟨Subalgebra.neg_mem _ hx.1, Subalgebra.neg_mem _ hx.2⟩`. Establish `gzero : good 0` using `⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩`. Establish `gone : good 1` using `⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩`. Establish `gstar : ∀ x, good x → good (star x)` using `fun x hx => ⟨hx.2, hx.1⟩`.

Establish `galg : ∀ c : ℂ, good (algebraMap ℂ (Pr (RadSp k r z z' π π')) c)` using `fun c => ⟨Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ (starRingEnd ℂ c)⟩`. Establish `gp : good (L.p l)`. Rewrite using `[hX.1 l]`. Conclude with `⟨hop 0, Subalgebra.neg_mem _ (hop 3)⟩`. Establish `gc : good (L.c l)`.

Rewrite using `[hX.2.2.1 l]`. Conclude with `⟨hop 1, hop 4⟩`. Establish `gci : good (L.ci l)`. Rewrite using `[hX.2.2.2.1 l]`. Conclude with `⟨hop 2, hop 5⟩`.

Establish `hTs : ∀ (Y : ℂ) (i j : Fin 2), good ((Wd.Ts (site L l) Y) i j)`. Introduce `Y i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `only [Wd.Ts, site, Formalism.YangianSpanCharacter.T.Tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one]`. Conclude with `gadd _ _ (galg Y) gp`.

Conclude with `gneg _ gc`. Conclude with `gci`. Conclude with `gzero`. Establish `hmulA : ∀ M N : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')), (∀ a b, good (M a b)) → (∀ a b, good (N a b)) → ∀ a b, good ((M * N) a b)`. Introduce `M N hM hN a b`.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun c _ => ?_)` and prove the remaining obligations. Conclude with `gmul _ _ (hM a c) (hN c b)`. Establish `hsumA : ∀ (ι : Type) (t : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))), (∀ i, ∀ a b, good (f i a b)) → ∀ a b, good ((∑ i ∈ t, f i) a b)`. Introduce `ι t f hf a b`.

Rewrite using `[Matrix.sum_apply]`. Conclude with `Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun i _ => hf i a b)`. Establish `heU : ∀ (x : S) (i j : Fin 2), ∀ a b, good ((Wd.eU (A` using `Pr (RadSp k r z z' π π')) x i j : Wd.SlopeTestRemainingChoices S _) a b) := by`. Introduce `x i j a b`. Unfold `Wd.eU`.

Simplify using `only [Matrix.of_apply]`. Use `split_ifs`. Conclude with `gone`. Conclude with `gzero`. Establish `hio : ∀ y, good y → ∀ a b, good ((Wd.io (S` using `S) y) a b) := by`.

Introduce `y hy a b`. Unfold `Wd.io`. Rewrite using `[Matrix.scalar_apply, Matrix.diagonal_apply]`. Use `split_ifs`. Conclude with `hy`.

Conclude with `gzero`. Establish `hvlet : ∀ lt : Wd.Letter ℂ S, ∀ a b, good ((Wd.vlet (site L l) lt) a b)`. Introduce `lt`. Unfold `Wd.vlet Wd.ins`. Use `hsumA _ _ _ (fun i => ?_)` and prove the remaining obligations.

Use `hsumA _ _ _ (fun j => ?_)` and prove the remaining obligations. Use `hmulA _ _ (heU _ i j) ?_` and prove the remaining obligations. Introduce `a b`. Unfold `Wd.lift0`. Rewrite using `[Matrix.map_apply]`.

Use `hio _ ?_ a b` and prove the remaining obligations. Use `split_ifs`. Conclude with `hTs _ i j`. Rewrite using `[Matrix.map_apply]`. Conclude with `gstar _ (hTs _ i j)`.

Establish `hbT : ∀ w' : List (Wd.Letter ℂ S), ∀ a b, good ((Wd.bT (site L l) w') a b)`. Introduce `w'`. Proceed by induction on `w' with`. Consider the case `nil`. Introduce `a b`.

Simplify using `only [Wd.bT]`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `gone`. Conclude with `gzero`.

Consider the case `cons lt w' ih`. Introduce `a b`. Simplify using `only [Wd.bT]`. Conclude with `hmulA _ _ (hvlet lt) ih a b`. Conclude with `(hbT w a b).1`.
-/
theorem boundary_torus_adjoin : CutSH.BTlAdjoin := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' X L hX S _ _ l w a b
  set Qa : Subalgebra ℂ (Module.End ℂ (RadSp k r z z' π π')) := Algebra.adjoin ℂ (Set.range (X.op l)) with hQa
  let good : Pr (RadSp k r z z' π π') → Prop := fun x => x.1 ∈ Qa ∧ x.2.unop ∈ Qa
  have hop : ∀ i, X.op l i ∈ Qa := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  have gmul : ∀ x y, good x → good y → good (x * y) := fun x y hx hy =>
    ⟨Subalgebra.mul_mem _ hx.1 hy.1, Subalgebra.mul_mem _ hy.2 hx.2⟩
  have gadd : ∀ x y, good x → good y → good (x + y) := fun x y hx hy =>
    ⟨Subalgebra.add_mem _ hx.1 hy.1, Subalgebra.add_mem _ hx.2 hy.2⟩
  have gneg : ∀ x, good x → good (-x) := fun x hx => ⟨Subalgebra.neg_mem _ hx.1, Subalgebra.neg_mem _ hx.2⟩
  have gzero : good 0 := ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  have gone : good 1 := ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
  have gstar : ∀ x, good x → good (star x) := fun x hx => ⟨hx.2, hx.1⟩
  have galg : ∀ c : ℂ, good (algebraMap ℂ (Pr (RadSp k r z z' π π')) c) := fun c =>
    ⟨Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ (starRingEnd ℂ c)⟩
  have gp : good (L.p l) := by
    rw [hX.1 l]
    exact ⟨hop 0, Subalgebra.neg_mem _ (hop 3)⟩
  have gc : good (L.c l) := by
    rw [hX.2.2.1 l]
    exact ⟨hop 1, hop 4⟩
  have gci : good (L.ci l) := by
    rw [hX.2.2.2.1 l]
    exact ⟨hop 2, hop 5⟩
  have hTs : ∀ (Y : ℂ) (i j : Fin 2), good ((Wd.Ts (site L l) Y) i j) := by
    intro Y i j
    fin_cases i <;> fin_cases j <;>
      simp only [Wd.Ts, site, Formalism.YangianSpanCharacter.T.Tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one]
    · exact gadd _ _ (galg Y) gp
    · exact gneg _ gc
    · exact gci
    · exact gzero
  have hmulA : ∀ M N : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')), (∀ a b, good (M a b)) → (∀ a b, good (N a b)) →
      ∀ a b, good ((M * N) a b) := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    refine Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun c _ => ?_)
    exact gmul _ _ (hM a c) (hN c b)
  have hsumA : ∀ (ι : Type) (t : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))),
      (∀ i, ∀ a b, good (f i a b)) → ∀ a b, good ((∑ i ∈ t, f i) a b) := by
    intro ι t f hf a b
    rw [Matrix.sum_apply]
    exact Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun i _ => hf i a b)
  have heU : ∀ (x : S) (i j : Fin 2), ∀ a b, good ((Wd.eU (A := Pr (RadSp k r z z' π π')) x i j : Wd.SlopeTestRemainingChoices S _) a b) := by
    intro x i j a b
    unfold Wd.eU
    simp only [Matrix.of_apply]
    split_ifs
    · exact gone
    · exact gzero
  have hio : ∀ y, good y → ∀ a b, good ((Wd.io (S := S) y) a b) := by
    intro y hy a b
    unfold Wd.io
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hy
    · exact gzero
  have hvlet : ∀ lt : Wd.Letter ℂ S, ∀ a b, good ((Wd.vlet (site L l) lt) a b) := by
    intro lt
    unfold Wd.vlet Wd.ins
    refine hsumA _ _ _ (fun i => ?_)
    refine hsumA _ _ _ (fun j => ?_)
    refine hmulA _ _ (heU _ i j) ?_
    intro a b
    unfold Wd.lift0
    rw [Matrix.map_apply]
    refine hio _ ?_ a b
    split_ifs
    · exact hTs _ i j
    · rw [Matrix.map_apply]
      exact gstar _ (hTs _ i j)
  have hbT : ∀ w' : List (Wd.Letter ℂ S), ∀ a b, good ((Wd.bT (site L l) w') a b) := by
    intro w'
    induction w' with
    | nil =>
      intro a b
      simp only [Wd.bT]
      rw [Matrix.one_apply]
      split_ifs
      · exact gone
      · exact gzero
    | cons lt w' ih =>
      intro a b
      simp only [Wd.bT]
      exact hmulA _ _ (hvlet lt) ih a b
  exact (hbT w a b).1

end Formalism.FourierDecayAlt.P
