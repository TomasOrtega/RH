import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.RefTup

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem qe_one_tup {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem twistPrimes_reference_tuple_eq_empty : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Q I.mu0 = ∅ := by
  intro B X I
  show QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅
  rw [I.trueColumn_tuple_trivial_eq_one]
  exact qe_one_tup I.sel

end GlobalTheory.Mem.Col2.RefTup
