import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.outsideS_elt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  first | exact @GlobalTheory.outsideS_elt | exact GlobalTheory.outsideS_elt | (intros; apply GlobalTheory.outsideS_elt <;> assumption)
