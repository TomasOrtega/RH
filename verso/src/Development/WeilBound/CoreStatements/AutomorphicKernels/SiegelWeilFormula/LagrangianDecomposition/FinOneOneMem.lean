import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩` and prove the remaining obligations. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0`. Rewrite using `[show (finOne F).1 = 0 from rfl, map_zero]`. Rewrite using `[show evFin F v (finOne F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]`. Conclude with `one_mem _`.

Simplify using the standard rewrite rules.
-/
theorem finOne_one_mem : finOne F • (1 : AE F E) ∈ intHat F E := by
  refine AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0
    rw [show (finOne F).1 = 0 from rfl, map_zero]
  · rw [show evFin F v (finOne F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
    exact one_mem _
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H u v`. Use `H (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v)` as an intermediate fact. Rewrite `this` using `[blk_map_apply]`. Then use the resulting hypothesis. Introduce `H u v`.

Rewrite using `[blk_apply]`. Generalize the expression as in `eB h u = x`. Generalize the expression as in `eB h v = y`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`. Conclude with `H x y`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply] split_ifs`. Conclude with `finOne_one_mem`. Simplify using the standard rewrite rules.
-/
theorem int_blk {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (∀ u v, finOne F • blk h M 1 u v ∈ intHat F E) ↔ ∀ u v, finOne F • M u v ∈ intHat F E := by
  constructor
  · intro H u v
    have := H (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v)
    rwa [blk_map_apply] at this
  · intro H u v
    rw [blk_apply]
    generalize eB h u = x
    generalize eB h v = y
    rcases x with x | x <;> rcases y with y | y
    · exact H x y
    · simp
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact finOne_one_mem
      · simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d n h Y b j hb hj`. Establish `hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1` using `fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)`. Introduce `k`. Rewrite using `[Subgroup.mem_comap, d.ok.stdK (j k)]`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]`.

Use `and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))` and prove the remaining obligations. Rewrite using `[blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose, Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]`.
-/
theorem kStd : KStd := by
  intro F E _ _ _ _ _ σ d n h Y b j hb hj
  have hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  intro k
  rw [Subgroup.mem_comap, d.ok.stdK (j k)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]
  refine and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))
  rw [blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose,
    Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]

end PositivityTheory.SiegelWeilFormula.Ald

end
