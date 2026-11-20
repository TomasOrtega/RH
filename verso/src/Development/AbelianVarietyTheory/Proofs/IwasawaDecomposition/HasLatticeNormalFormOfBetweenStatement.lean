import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatticeNormalFormOfBetween
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHasLatticeNormalFormOfBetween.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.hasLatticeNormalForm_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  first | exact @GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | exact GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | (intros; apply GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between <;> assumption)
