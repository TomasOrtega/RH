import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts.
-/
private theorem UpperTheory.star_diagonal_entry_eq {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    star (mt γ 0 0) = mt γ 1 1 := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) (γ : GL (Fin 2) (Lsq K Δ)) =
      (wJ Δ)⁻¹ * (γ : GL (Fin 2) (Lsq K Δ)) * ((wJ Δ)⁻¹)⁻¹ := γ.2
  have h1 := congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) h
  have hw : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0] := rfl
  have hw' : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0] := rfl
  simp only [inv_inv, Units.val_mul, hw, hw'] at h1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] using h1

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.orbitalFiber_hasTraceLaw :
    UpperTheory.V.Z.Sym.Glob.Fib.HasTrLaw := by
  intro K _ Δ γ
  have hmem : γ ∈ SU Δ ↔ (mt γ).det = 1 := by
    rw [SU, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hmem]
    constructor
    · intro hd
      refine ⟨(mt γ).trace.re, hd, ?_⟩
      have := UpperTheory.star_diagonal_entry_eq γ
      ext
      · simp
      · rw [Matrix.trace_fin_two, ← this]
        simp
    · rintro ⟨s, hs, _⟩
      exact hs
  · intro s s' hs hs'
    have := congrArg QuadraticAlgebra.re (hs.2.symm.trans hs'.2)
    simpa using this
  · intro h s
    have e : mt (h * γ * h⁻¹) = ((h : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt γ *
        (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := rfl
    unfold HasTr
    rw [e, Matrix.det_units_conj, Matrix.trace_units_conj]
