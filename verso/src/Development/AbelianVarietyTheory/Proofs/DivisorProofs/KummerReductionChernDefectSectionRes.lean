import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

/- English proof (translation)
Introduce `Q q _ hqQ U u hQ V g`. Establish `hQV : IsUnit (Q : Γ(V, ⊤))`. Use `hQ.map g.appTop.hom` as an intermediate fact. Simplify using `using this`. Apply `(GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1` to reduce the goal to its premises.

Use `loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_` and prove the remaining obligations. Introduce and unpack `W h ⟨v, hv⟩`. Establish `hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u)`. Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`. Rewrite using `[hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]`.

Use `GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_` and prove the remaining obligations. Rewrite using `[hv]`. Use `ext`. Apply the tactic sequence `simp [Scheme.Hom.comp_appTop] <;> rfl`.
-/
theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
