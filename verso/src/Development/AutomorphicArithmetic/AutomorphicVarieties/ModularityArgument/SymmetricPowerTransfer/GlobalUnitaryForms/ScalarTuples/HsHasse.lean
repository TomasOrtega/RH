import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open UpperTheory.V.Z.Sym.Loc in
/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Evaluate the numerical expressions. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem hs_eq_one_iff {K : Type} [Field K] (d x : K) :
    hs d x = 1 ↔ ∃ a b : K, x = a ^ 2 - d * b ^ 2 := by
  unfold hs
  constructor
  · intro h
    by_contra hn
    rw [if_neg (fun ⟨a, b, e⟩ => hn ⟨a, b, e.symm⟩)] at h
    norm_num at h
  · rintro ⟨a, b, e⟩
    exact if_pos ⟨a, b, e.symm⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Glob.hsHasse :
    UpperTheory.V.Z.Sym.Glob.HsHasse := by
  intro F _ _ d x hd hx hr hf
  rw [hs_eq_one_iff]
  exact GlobalTheory.QNorm.hasseNormSt F d x hd hx (fun σ => (hs_eq_one_iff _ _).1 (hr σ))
    (fun v => (hs_eq_one_iff _ _).1 (hf v))
