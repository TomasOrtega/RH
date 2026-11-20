import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemberLevelPrimeNotUnderTwistPrime.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.memberLevelPrime_not_under_twistPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | (intros; apply GlobalTheory.Mem.Col2.ChEx.T_notMem_qv <;> assumption)
