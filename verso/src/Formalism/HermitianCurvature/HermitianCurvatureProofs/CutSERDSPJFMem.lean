import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D F hF hcs hts`. Establish `hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g` using `fun g hg => (hts hg).2.2`. Take `⟨ε, hε, hεle⟩` from `hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos`. Establish `hnice : NiceAll D F`. Use `⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Assume the negation of the conclusion as `h`. Conclude with `hg (subset_tsupport _ h)`. Introduce `g _ hg`. Conclude with `hεle g (subset_tsupport _ hg)`.

Use `⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩` and prove the remaining obligations. Introduce `g _ hne`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `hne` to reduce the goal to its premises.

Use `show ∫ p, _ ∂D.μSS = 0`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [B5.ae_inSS D] with p hp`. Establish `h0 : F (B.sgs p g) = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hno p hp (subset_tsupport _ h)`. Use `show _ • _ = (0 : Wq →L[ℂ] Wp)`. Simplify using `only [B.sgs] at h0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
