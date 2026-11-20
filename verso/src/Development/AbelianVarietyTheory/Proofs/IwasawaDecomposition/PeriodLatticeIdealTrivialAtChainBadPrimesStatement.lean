import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPeriodLatticeIdealTrivialAtChainBadPrimes.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.aaUnit_sall | exact GlobalTheory.Mem.Col2.AdT.aaUnit_sall | (intros; apply GlobalTheory.Mem.Col2.AdT.aaUnit_sall <;> assumption)
