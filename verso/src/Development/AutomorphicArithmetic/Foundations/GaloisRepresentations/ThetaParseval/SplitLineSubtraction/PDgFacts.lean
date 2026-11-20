import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc

noncomputable section

open Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

section

variable {Γ k : Type} [Group Γ] [Field k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dg_val {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = Matrix.diagonal fun i => (a i g : k) := rfl

/- English proof (translation)
Establish `key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W`. Introduce `W g v hv`. Establish `: ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v`. Use extensionality with `i`. Use `fin_cases i`.

Simplify using `[dg_val, Matrix.mulVec_diagonal]`. Rewrite using `[this]`. Conclude with `W.smul_mem _ hv`. Introduce `W _`. Take `⟨W', hW'⟩` from `exists_isCompl W`.

Conclude with `⟨W', key W', hW'⟩`.
-/
private theorem ss_dg_one (b : Fin 1 → Γ →* kˣ) : IsSSRep (dg b) := by
  have key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W := by
    intro W g v hv
    have : ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v := by
      ext i
      fin_cases i
      simp [dg_val, Matrix.mulVec_diagonal]
    rw [this]
    exact W.smul_mem _ hv
  intro W _
  obtain ⟨W', hW'⟩ := exists_isCompl W
  exact ⟨W', key W', hW'⟩

/- English proof (translation)
Use extensionality with `g : 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`.

Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]`. Both sides reduce to the same expression. Introduce `h`.

Establish `h'` using `congrArg Fin.val h`. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at h'`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Establish `h'` using `congrArg Fin.val h`.

Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at h'`. Use linear arithmetic over natural numbers and integers. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression.
-/
private theorem dg_succ {t : ℕ} (a : Fin (t + 1) → Γ →* kˣ) :
    dg a = sumRep (dg fun i : Fin t => a i.castSucc) (dg fun _ : Fin 1 => a (Fin.last t)) := by
  ext g : 1
  apply Units.ext
  rw [GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact GlobalTheory.BCGal.ss_zero _`. Consider the case `succ t ih`. Rewrite using `[dg_succ]`. Conclude with `GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)`.
-/
private theorem ss_dg {t : ℕ} (a : Fin t → Γ →* kˣ) : IsSSRep (dg a) := by
  induction t with
  | zero => exact GlobalTheory.BCGal.ss_zero _
  | succ t ih =>
    rw [dg_succ]
    exact GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)

end

/- English proof (translation)
Introduce `Γ k _ _ t a`. Use `⟨ss_dg a, fun g => ?_⟩` and prove the remaining obligations. Use `show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _`. Rewrite using `[dg_val, Matrix.charpoly_diagonal]`.
-/
theorem dgFacts_holds : DgFacts := by
  intro Γ k _ _ t a
  refine ⟨ss_dg a, fun g => ?_⟩
  show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _
  rw [dg_val, Matrix.charpoly_diagonal]

end UpperTheory.Gal.TP.Sub

end
