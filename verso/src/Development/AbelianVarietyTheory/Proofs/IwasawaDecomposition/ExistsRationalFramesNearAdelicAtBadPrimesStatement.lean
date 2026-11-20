import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsRationalFramesNearAdelicAtBadPrimes.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.frNear_exists | exact GlobalTheory.Mem.Col2.AdT.frNear_exists | (intros; apply GlobalTheory.Mem.Col2.AdT.frNear_exists <;> assumption)
