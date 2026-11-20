import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LdpContDiffOn

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp GlobalTheory.CompanionTheory.WaveCp.Rep GlobalTheory.CompanionTheory.WaveCp.Rep.Mol
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth

/- English proof (translation)
The claim follows from `contDiff_apply_apply ℝ ℂ i j`.
-/
theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ ℂ i j

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiff.sum fun σ _ => contDiff_const.mul ?_` and prove the remaining obligations. Conclude with `contDiff_prod fun i _ => hM _ _`.
-/
theorem contDiff_det {n : ℕ} {M : Mat n → Mat n} (hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)) :
    ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM _ _

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Use `contDiff_det fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Simplify `contDiff_const` using `[Matrix.updateRow_self]`.

Apply the tactic sequence `simpa [Matrix.updateRow_ne h] using contDiff_entry a b`.
-/
theorem contDiff_adjugate_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne h] using contDiff_entry a b

/- English proof (translation)
Establish `hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n)` using `(contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)`. Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_`. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv]`.
-/
theorem contDiffOn_inv {n : ℕ} : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth
