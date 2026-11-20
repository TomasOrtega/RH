import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERD

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D hr ε s G`. Establish `h1 : 1 < r + 2` using `by omega`. Use `⟨fun hG => Formalism.FourierDecayAlt.P.PBFV.good_fsv_dmin D ε s h1 G hG, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ p : B.SS k r, D.inSS p → ∀ g, fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩)` using `fun p hp g => by`. Rewrite using `[Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]`.

Simplify using `only [resG]`. Rewrite using `[show wvG D.z D.z' s G = fun g => fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • G g from rfl, Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv G]`. Rewrite using `[Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord D.z_mem D.z'_mem hr y.1 hy.2.1 h1]`. Conclude with `smul_comm _ _ _`.
-/
theorem radial_wave_identity : RDWave := by
  intro k r Wp Wq _ _ _ _ _ _ D hr ε s G
  have h1 : 1 < r + 2 := by omega
  refine ⟨fun hG => Formalism.FourierDecayAlt.P.PBFV.good_fsv_dmin D ε s h1 G hG, fun y hy => ?_⟩
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  simp only [resG]
  rw [show wvG D.z D.z' s G = fun g => fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • G g from rfl,
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv G]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord D.z_mem D.z'_mem hr y.1 hy.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
