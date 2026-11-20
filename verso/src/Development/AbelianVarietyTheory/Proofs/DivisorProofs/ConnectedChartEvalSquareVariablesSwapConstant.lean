import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.EvSquare

noncomputable def constAlg (σ : Type) (k : Type) [CommRing k] : MvPowerSeries σ k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries σ k →+* k) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

/- English proof (translation)
Establish `h` using `GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ k (evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero)) (constAlg σ k) (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact IsNilpotent.zero) (fun i => by rw [GlobalTheory.T.powerSerie …`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem evA_zero (k : Type) [CommRing k] (σ : Type) [Finite σ] (f : MvPowerSeries σ k) :
    evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero) f = constantCoeff f := by
  have h := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ k (evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero))
    (constAlg σ k) (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact IsNilpotent.zero)
    (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; simp [constAlg])
  rw [h]; rfl

/- English proof (translation)
Introduce `p k _ d G c n`. Establish `hX : ∀ t, c.ev₂ n (X t) = c.x₂ n t` using `fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ t`. Establish `hN : ∀ t, IsNilpotent (c.ev₂ n (X t))` using `fun t => by rw [hX]; exact c.nil₂ n t`. Use `⟨fun f => ?_, fun f => ?_, fun s => ?_, fun s => ?_⟩` and prove the remaining obligations. Establish `hy : ∀ i, IsNilpotent (c.x n i ⊗ₜ[k] (1 : G.A n))` using `fun i => c.nil₂ n (Sum.inl i)`.

Establish `e1` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN (fun i => X (Sum.inl i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f`. Establish `e2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n) Algebra.TensorProduct.includeLeft (c.x n) (c.nil n) _ hy (fun i => rfl) f`. Unfold `inL`. Rewrite using `[e1, ← e2]`. Both sides reduce to the same expression.

Establish `hy : ∀ i, IsNilpotent ((1 : G.A n) ⊗ₜ[k] c.x n i)` using `fun i => c.nil₂ n (Sum.inr i)`. Establish `e1` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN (fun i => X (Sum.inr i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f`. Establish `e2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n) Algebra.TensorProduct.includeRight (c.x n) (c.nil n) _ hy (fun i => rfl) f`. Unfold `inR`. Rewrite using `[e1, ← e2]`.

Both sides reduce to the same expression. Set `g : G.A n ⊗[k] G.A n →ₐ[k] G.A n ⊗[k] G.A n` to `(Algebra.TensorProduct.comm k (G.A n) (G.A n)).toAlgHom`. Establish `hy : ∀ i, IsNilpotent (g (c.x₂ n i))` using `fun i => (c.nil₂ n i).map g`. Apply the tactic sequence `have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN (Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i))) (fun i => by cases i <;> exact constantCoeff_X _) _ hy (fun i => by`. Consider the cases of `i with`.

Consider the case `inl i => rw [Sum.elim_inl, hX]`. Simplify using `[g, Chart.x₂]`. Consider the case `inr i => rw [Sum.elim_inr, hX]`. Simplify using `[g, Chart.x₂]) s`. Establish `e2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n ⊗[k] G.A n) g (c.x₂ n) (c.nil₂ n) _ hy (fun i => rfl) s`.

Unfold `Katz.swap at2`. Rewrite using `[e1, ← e2]`. Both sides reduce to the same expression. Set `L : G.A n ⊗[k] G.A n →ₐ[k] k` to `Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _)`. Establish `e2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 k L (c.x₂ n) (c.nil₂ n) (fun _ => (0 : k)) (fun _ => IsNilpotent.zero) (fun i => by`.

Consider the cases of `i with`. Consider the case `inl i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]`. Consider the case `inr i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]) s`. Express the relevant statement in the definitionally equal form `L (c.ev₂ n s) = _`. Unfold `Chart.ev₂`.

Rewrite using `[e2, evA_zero]`.
-/
theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p k _ d G c n
  have hX : ∀ t, c.ev₂ n (X t) = c.x₂ n t := fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ t
  have hN : ∀ t, IsNilpotent (c.ev₂ n (X t)) := fun t => by rw [hX]; exact c.nil₂ n t
  refine ⟨fun f => ?_, fun f => ?_, fun s => ?_, fun s => ?_⟩
  · have hy : ∀ i, IsNilpotent (c.x n i ⊗ₜ[k] (1 : G.A n)) := fun i => c.nil₂ n (Sum.inl i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inl i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeLeft (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inL; rw [e1, ← e2]; rfl
  · have hy : ∀ i, IsNilpotent ((1 : G.A n) ⊗ₜ[k] c.x n i) := fun i => c.nil₂ n (Sum.inr i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inr i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeRight (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inR; rw [e1, ← e2]; rfl
  · let g : G.A n ⊗[k] G.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      (Algebra.TensorProduct.comm k (G.A n) (G.A n)).toAlgHom
    have hy : ∀ i, IsNilpotent (g (c.x₂ n i)) := fun i => (c.nil₂ n i).map g
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)))
      (fun i => by cases i <;> exact constantCoeff_X _) _ hy
      (fun i => by
        cases i with
        | inl i => rw [Sum.elim_inl, hX]; simp [g, Chart.x₂]
        | inr i => rw [Sum.elim_inr, hX]; simp [g, Chart.x₂]) s
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n ⊗[k] G.A n)
      g (c.x₂ n) (c.nil₂ n) _ hy (fun i => rfl) s
    unfold Katz.swap at2
    rw [e1, ← e2]; rfl
  · let L : G.A n ⊗[k] G.A n →ₐ[k] k := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n))
      (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _)
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 k
      L (c.x₂ n) (c.nil₂ n) (fun _ => (0 : k)) (fun _ => IsNilpotent.zero)
      (fun i => by
        cases i with
        | inl i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]
        | inr i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]) s
    change L (c.ev₂ n s) = _
    unfold Chart.ev₂; rw [e2, evA_zero]

end GlobalTheory.EvSquare
