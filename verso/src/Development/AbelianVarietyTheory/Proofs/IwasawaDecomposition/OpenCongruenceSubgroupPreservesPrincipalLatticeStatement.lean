import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OpenPrinc.open_princ` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FOpenCongruenceSubgroupPreservesPrincipalLattice.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.open_congruence_subgroup_preserves_principal_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), ∃ N : ℕ, 0 < N ∧ ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ J v S.Lb → (∀ y ∈ Formalism.L2.Herm.locL v S.Lb, ∃ z ∈ Formalism.L2.Herm.locL v S.Lb, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (N : E ⊗[F] v.adicCompletion F) • z) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.OpenPrinc.open_princ | exact GlobalTheory.OpenPrinc.open_princ | (intros; apply GlobalTheory.OpenPrinc.open_princ <;> assumption)
