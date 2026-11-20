import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false

noncomputable section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]`. Both sides reduce to the same expression.
-/
theorem cech_d_eq_dZ (P : PM.{0} R ι) (n : ℕ) (c : P.cech.X n) :
    P.cech.d n c = dZ P.M (fun h x => P.res h x) n c := by
  funext i
  simp only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]
  rfl

/- English proof (translation)
Rewrite using `[cech_d_eq_dZ]`. Use function extensionality and compare the values at `i`. Establish `key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) = P.res (Finset.empty_subset (ent i)) x` using `fun k => P.res_comp _ _ x`. Simplify using `only [dZ, Fin.sum_univ_two, key]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem cech_d_aug (P : PM.{0} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  rw [cech_d_eq_dZ]
  funext i
  have key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) =
      P.res (Finset.empty_subset (ent i)) x := fun k => P.res_comp _ _ x
  simp only [dZ, Fin.sum_univ_two, key]
  simp
  rfl

/- English proof (translation)
Introduce `R _ ι _ P h`. Take `⟨h0, h1, h2⟩` from `h`. Use `⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `h0 x fun i => congrFun hx i`.

Take `⟨x, hx⟩` from `h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)`. Conclude with `⟨x, (funext hx).trans (one_smul _ _).symm⟩`. Take `⟨b, hb⟩` from `h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)`. Conclude with `⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩`.
-/
theorem ex_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι),
    ExP P.M (fun h x => P.res h x) → P.Ex := by
  intro R _ ι _ P h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [one_smul]
    exact h0 x fun i => congrFun hx i
  · obtain ⟨x, hx⟩ := h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)
    exact ⟨x, (funext hx).trans (one_smul _ _).symm⟩
  · obtain ⟨b, hb⟩ := h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)
    exact ⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.SurjectionOntoH4
