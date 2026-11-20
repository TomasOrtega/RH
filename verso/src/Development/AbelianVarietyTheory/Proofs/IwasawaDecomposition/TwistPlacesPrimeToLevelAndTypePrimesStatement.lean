import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTwistPlacesPrimeToLevelAndTypePrimes.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | exact GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | (intros; apply GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad <;> assumption)
