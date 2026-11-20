import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
