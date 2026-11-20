import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalGaloisDataShaLengthEq
import Mathlib
import Formalism.GaloisCohomology.Statement
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLocalGaloisDataShaLengthEq.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.exists_localGaloisData_shaLength_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ) [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l), ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  first | exact @GlobalTheory.ShaTransport.exists_lData_shaLen_eq | exact GlobalTheory.ShaTransport.exists_lData_shaLen_eq | (intros; apply GlobalTheory.ShaTransport.exists_lData_shaLen_eq <;> assumption)
