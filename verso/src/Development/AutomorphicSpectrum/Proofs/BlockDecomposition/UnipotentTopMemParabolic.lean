import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.TopCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(ext; simp [GlobalTheory.BZMir.Leib.ePG])`.
-/
theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  first
  | rfl
  | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

/- English proof (translation)
Establish `h : GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc a⟩ = ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans ((Equiv.sumAssoc (Fin i) (Fin 1) (Fin t)).trans ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).tr …` using `rfl`. Rewrite using `[h]`. Use `ext`. Simplify using `[finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  have h : GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc a⟩ =
      ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans
        ((Equiv.sumAssoc (Fin i) (Fin 1) (Fin t)).trans
          ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).trans
            ((Equiv.sumAssoc (Fin i) (Fin t) (Fin 1)).symm.trans
              ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv)))))
        (Sum.inl (Fin.castSucc a)) := rfl
  rw [h]
  ext
  simp [finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq]`. Conclude with `Fin.castSucc_ne_last _`.
-/
theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq]
  exact Fin.castSucc_ne_last _

/- English proof (translation)
Use `show ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k)) ∈ GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)`. Rewrite using `[GlobalTheory.SmGL.mem_parab_iff]`. Introduce `a b p q hba`. Apply the tactic sequence `cases a <;> cases b`. Apply the tactic sequence `all_goals first`.

Consider the case `exact absurd hba (by decide)`. Consider the case `(simp at hba; done)`. Consider the case `skip`. Establish `hne : GlobalTheory.BZMir.Leib.ePG i t ⟨true, p⟩ ≠ GlobalTheory.BZMir.Leib.ePG i t ⟨false, q⟩`. Introduce `h`.

Establish `h' : true = false` using `congrArg Sigma.fst ((GlobalTheory.BZMir.Leib.ePG i t).injective h)`. Consider the cases of `h'`. Establish `hr` using `GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq i t p`. Rewrite using `[GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, Matrix.one_apply_ne hne, zero_add, hr]`. Simplify using `only [GlobalTheory.BZMir.colMat]`.

Use `split_ifs`. Rewrite using `[Fin.lastCases_castSucc]`. Simplify using `[GlobalTheory.CompanionTheory.BZPsiPG.topV]`. Both sides reduce to the same expression.
-/
theorem mem (i t : ℕ) (x : Fin i → k) : uM k (i + t) (topV k i t x) ∈ HPG k i t := by
  show ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k)) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b p q hba
  cases a <;> cases b
  all_goals first
    | exact absurd hba (by decide)
    | (simp at hba; done)
    | skip
  have hne : GlobalTheory.BZMir.Leib.ePG i t ⟨true, p⟩ ≠ GlobalTheory.BZMir.Leib.ePG i t ⟨false, q⟩ := by
    intro h
    have h' : true = false := congrArg Sigma.fst ((GlobalTheory.BZMir.Leib.ePG i t).injective h)
    cases h'
  have hr := GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq i t p
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, Matrix.one_apply_ne hne, zero_add, hr]
  simp only [GlobalTheory.BZMir.colMat]
  split_ifs
  · rw [Fin.lastCases_castSucc]
    simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
  · rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = _`. Establish `h1 : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b`.

Simplify using `[Matrix.one_apply]`. Establish `h2 : GlobalTheory.BZMir.colMat k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = GlobalTheory.BZMir.colMat k i x a b`. Simplify using `only [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff]`. Use `split_ifs with hb`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => rw [GlobalTheory.BZMir.Leib.ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]`. Consider the case `cast c`. Rewrite using `[GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_false_eq, Fin.lastCases_castSucc, Fin.lastCases_castSucc]`. Simplify using `[GlobalTheory.CompanionTheory.BZPsiPG.topV]`. Both sides reduce to the same expression.

Rewrite using `[GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, h1, h2]`.
-/
theorem fst (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).1 = uM k i x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = _
  have h1 : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := by
    simp [Matrix.one_apply]
  have h2 : GlobalTheory.BZMir.colMat k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      GlobalTheory.BZMir.colMat k i x a b := by
    simp only [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff]
    split_ifs with hb
    · induction a using Fin.lastCases with
      | last => rw [GlobalTheory.BZMir.Leib.ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast c =>
        rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_false_eq, Fin.lastCases_castSucc,
          Fin.lastCases_castSucc]
        simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
    · rfl
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry,
    GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, h1, h2]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, b⟩) = (1 : Matrix …`. Rewrite using `[GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry]`. Simplify using `only [GlobalTheory.BZMir.colMat, if_neg (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_ne_last i t b), add_zero]`.

Simplify using `[Matrix.one_apply]`.
-/
theorem snd (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).2 = 1 := by
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, b⟩) =
      (1 : Matrix (Fin t) (Fin t) k) a b
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry]
  simp only [GlobalTheory.BZMir.colMat, if_neg (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_ne_last i t b), add_zero]
  simp [Matrix.one_apply]

/- English proof (translation)
Introduce `k _ _ _ _ i t x`. Conclude with `⟨GlobalTheory.CompanionTheory.BZPsiPG.TopCol.mem i t x, Prod.ext (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.fst i t x) (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.snd i t x)⟩`.
-/
theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  intro k _ _ _ _ i t x
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.TopCol.mem i t x,
    Prod.ext (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.fst i t x)
      (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.snd i t x)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.TopCol

end
