import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lie, Matrix.of_apply]`. Express the relevant statement in the definitionally equal form `Fin (ρ.M + σ.M) at i j`. Express the relevant statement in the definitionally equal form `∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _`. Take `⟨x, rfl⟩` from `finSumFinEquiv.surjective i`.

Take `⟨y, rfl⟩` from `finSumFinEquiv.surjective j`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]`.
-/
theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
