import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsGaloisConjugatesHeckeCharTrivialOnRealIdel.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles : ∀ (D : D7) (Q : Par D) (χ₀ : (AE D)ˣ →* Circle), IsHeckeChar D χ₀ → (∀ a, χ₀ (idF D a) = 1) → (∀ x, FinUnit x → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y) → ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, χ Q.c.F.val.toRingHom = χ₀ ∧ ∀ σ, IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ χ₀ (χ σ) := by
  first | exact @GlobalTheory.HeckeConj.exists_conjugates | exact GlobalTheory.HeckeConj.exists_conjugates | (intros; apply GlobalTheory.HeckeConj.exists_conjugates <;> assumption)
