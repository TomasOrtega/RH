import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

open UpperTheory.V.Af UpperTheory.V.Af.Gu

/- English proof (translation)
Introduce `Γ k _ _ a b r r' ha hb hirr`. Set `W : Submodule k (Fin (a + b) → k)` to `{ carrier := {v | ∀ j : Fin b, v (Fin.natAdd a j) = 0} add_mem' := by`. Introduce `x y hx hy j`. Simplify using `[hx j, hy j]`. Use the proof step `zero_mem' := by`.

Introduce `j`. Both sides reduce to the same expression. Use the proof step `smul_mem' := by`. Introduce `c x hx j`. Simplify using `[hx j] }`.

Establish `hinv : Formalism.MainNotions.N.IsInv (Formalism.MainNotions.SumRepresentations.At.sumRep r r') W`. Introduce `g v hv j`. Establish `hM : ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a+b)) k) : Matrix (Fin (a+b)) (Fin (a+b)) k) = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (((r g) : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) (0 : Matrix (Fin a) (Fin b) k) (0 : Matri …` using `rfl`. Rewrite using `[hM]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]`.

Rewrite using `[Fin.sum_univ_add]`. Simplify using `[hv _]`. Establish `hne : W ≠ ⊥`. Introduce `h`. Establish `hmem : (Pi.single (Fin.castAdd b ⟨0, ha⟩) (1 : k) : Fin (a + b) → k) ∈ W`.

Introduce `j`. Rewrite using `[Pi.single_apply, if_neg]`. Introduce `h'`. Conclude with `absurd h' (Fin.ne_of_val_ne (by simp; omega))`. Rewrite `hmem` using `[h, Submodule.mem_bot]`.

Use `congrFun hmem (Fin.castAdd b ⟨0, ha⟩)` as an intermediate fact. Simplify using `at this`. Establish `hntop : W ≠ ⊤`. Introduce `h`. Establish `hmem : (Pi.single (Fin.natAdd a ⟨0, hb⟩) (1 : k) : Fin (a + b) → k) ∈ W`.

Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Use `hmem ⟨0, hb⟩` as an intermediate fact. Simplify using `at this`. Break down `hirr.2.2 W le_top hinv with h | h` into its components or cases.

Conclude with `hne h`. Conclude with `hntop h`.
-/
theorem UpperTheory.finiteSum_reduction :
    SumRed := by
  intro Γ k _ _ a b r r' ha hb hirr
  let W : Submodule k (Fin (a + b) → k) :=
    { carrier := {v | ∀ j : Fin b, v (Fin.natAdd a j) = 0}
      add_mem' := by
        intro x y hx hy j
        simp [hx j, hy j]
      zero_mem' := by
        intro j
        rfl
      smul_mem' := by
        intro c x hx j
        simp [hx j] }
  have hinv : Formalism.MainNotions.N.IsInv (Formalism.MainNotions.SumRepresentations.At.sumRep r r') W := by
    intro g v hv j
    have hM : ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a+b)) k) : Matrix (Fin (a+b)) (Fin (a+b)) k) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (((r g) : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) (0 : Matrix (Fin a) (Fin b) k)
            (0 : Matrix (Fin b) (Fin a) k) (((r' g) : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) := rfl
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    simp [hv _]
  have hne : W ≠ ⊥ := by
    intro h
    have hmem : (Pi.single (Fin.castAdd b ⟨0, ha⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      intro j
      rw [Pi.single_apply, if_neg]
      intro h'
      exact absurd h' (Fin.ne_of_val_ne (by simp; omega))
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem (Fin.castAdd b ⟨0, ha⟩)
    simp at this
  have hntop : W ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (Fin.natAdd a ⟨0, hb⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      rw [h]
      exact Submodule.mem_top
    have := hmem ⟨0, hb⟩
    simp at this
  rcases hirr.2.2 W le_top hinv with h | h
  · exact hne h
  · exact hntop h
