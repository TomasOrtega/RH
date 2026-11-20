import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
/- English proof (translation)
Establish `h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) (γ : GL (Fin 2) (Lsq K Δ)) = (wJ Δ)⁻¹ * (γ : GL (Fin 2) (Lsq K Δ)) * ((wJ Δ)⁻¹)⁻¹` using `γ.2`. Establish `h1` using `congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) h`. Establish `hw : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0]` using `rfl`. Establish `hw' : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0]` using `rfl`. Simplify using `only [inv_inv, Units.val_mul, hw, hw'] at h1`.

Simplify `h1` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply]`.
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
Introduce `K _ Δ γ`. Establish `hmem : γ ∈ SU Δ ↔ (mt γ).det = 1`. Rewrite using `[SU, MonoidHom.mem_ker, Units.ext_iff]`. Both sides reduce to the same expression. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `hd`. Use `⟨(mt γ).trace.re, hd, ?_⟩` and prove the remaining obligations. Use `UpperTheory.star_diagonal_entry_eq γ` as an intermediate fact.

Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.trace_fin_two, ← this]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨s, hs, _⟩`.

Conclude with `hs`. Introduce `s s' hs hs'`. Use `congrArg QuadraticAlgebra.re (hs.2.symm.trans hs'.2)` as an intermediate fact. Simplify using `using this`. Introduce `h s`.

Establish `e : mt (h * γ * h⁻¹) = ((h : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt γ * (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ))` using `rfl`. Unfold `HasTr`. Rewrite using `[e, Matrix.det_units_conj, Matrix.trace_units_conj]`.
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
