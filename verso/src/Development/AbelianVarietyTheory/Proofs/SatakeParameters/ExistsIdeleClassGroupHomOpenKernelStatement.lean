import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsIdeleClassGroupHomOpenKernel.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.exists_ideleClassGroupHom_open_kernel : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.exists_ideleClassHom | exact GlobalTheory.exists_ideleClassHom | (intros; apply GlobalTheory.exists_ideleClassHom <;> assumption)
