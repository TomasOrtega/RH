import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.ConstIff.constituent_hcRep_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsConstituentHarishChandraRepIffPairingNeZero.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | exact GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | (intros; apply GlobalTheory.GLq.ConstIff.constituent_hcRep_iff <;> assumption)
