import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

variable (E r s) in

def blockOne (x : Lie E r) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks (Matrix.of x) 0 0 1))

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E)) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j'`.

Conclude with `contDiff_apply_apply ℝ (Cinf E) i' j'`. Conclude with `contDiff_const`. Conclude with `contDiff_const`. Conclude with `contDiff_const`.
-/
theorem contDiff_blockOne : ContDiff ℝ (⊤ : ℕ∞) (blockOne E r s) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · exact contDiff_apply_apply ℝ (Cinf E) i' j'
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.val_emb₂]`. Both sides reduce to the same expression.
-/
theorem blockOne_val (y : GL (Fin r) (Cinf E)) :
    blockOne E r s (toL (y : Matrix (Fin r) (Fin r) (Cinf E))) =
      toL ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := by
  rw [GlobalTheory.SmGL.val_emb₂]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩`.
-/
theorem exists_val_of_mem_invSet {x : Lie E r} (hx : x ∈ invSet E r) :
    ∃ y : GL (Fin r) (Cinf E), x = toL (y : Matrix (Fin r) (Fin r) (Cinf E)) :=
  ⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩

/- English proof (translation)
The claim follows from `show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit`.
-/
theorem toL_val_mem_invSet (y : GL (Fin r) (Cinf E)) :
    toL (y : Matrix (Fin r) (Fin r) (Cinf E)) ∈ invSet E r :=
  show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit

/- English proof (translation)
Introduce `g`. Establish `hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s))`. Introduce `x hx`. Take `⟨y, rfl⟩` from `exists_val_of_mem_invSet hx`. Rewrite using `[blockOne_val]`.

Conclude with `toL_val_mem_invSet _`. Establish `hcomp` using `(hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps`. Use `hcomp.congr fun x hx => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `exists_val_of_mem_invSet hx`. Rewrite using `[Function.comp_apply, blockOne_val, chart_val, chart_val]`.

Establish `e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1))`. Rewrite using `[← lev_infGL, map_one]`. Rewrite using `[← e1, lev_mul_one]`.
-/
theorem sm_lev_slice (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ)
    (hF : F ∈ Sm E (r + s)) : (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  intro g
  have hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
    rw [blockOne_val]
    exact toL_val_mem_invSet _
  have hcomp := (hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps
  refine hcomp.congr fun x hx => ?_
  obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
  rw [Function.comp_apply, blockOne_val, chart_val, chart_val]
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [← e1, lev_mul_one]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
