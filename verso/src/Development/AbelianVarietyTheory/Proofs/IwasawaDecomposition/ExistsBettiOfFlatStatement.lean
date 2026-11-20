import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBettiOfFlat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsBettiOfFlat.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_betti_of_flat : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn), IsFlat (Φ.C k) (DV.tauEmb D τ) σ → ∃ b, IsBetti s Φ L k τ σ b := by
  first | exact @GlobalTheory.ShFam.Pad.exists_isBetti_of_isFlat | exact GlobalTheory.ShFam.Pad.exists_isBetti_of_isFlat | (intros; apply GlobalTheory.ShFam.Pad.exists_isBetti_of_isFlat <;> assumption)
