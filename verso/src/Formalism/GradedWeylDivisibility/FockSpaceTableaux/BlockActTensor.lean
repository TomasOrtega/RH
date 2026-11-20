import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[blockEmb, blockAct, rowAct, map_sum, rename_C]`.
-/
theorem ldtensor_blockAct_comp (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [blockEmb, blockAct, rowAct, map_sum, rename_C]

/- English proof (translation)
Conclude with `AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F`.
-/
theorem ldtensor_blockAct_blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by
  exact AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F

/- English proof (translation)
Introduce `R K _ _ _ S _ k n g`. Use `⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩` and prove the remaining obligations. Introduce `M M' hMM' P hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨F, hF, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))`.

Consider the case `zero`. Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[← algebraMap_smul K a x, map_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem block_action_tensor : BlockActTensor := by
  intro R K _ _ _ S _ k n g
  refine ⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩
  intro M M' hMM' P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.GradedWeylDivisibility
