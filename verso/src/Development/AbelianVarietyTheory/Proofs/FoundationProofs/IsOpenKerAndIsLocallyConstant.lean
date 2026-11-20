import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

namespace GlobalTheory.OpenKernelLocallyConstant

/- English proof (translation)
Establish `hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω))`. Establish `halg : Algebra.IsAlgebraic ℚ Ω` using `IsAlgClosure.isAlgebraic`. Set `S : Set Ω` to `{z | z ^ N = 1}`. Establish `hS : S.Finite`. Use `(Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_` and prove the remaining obligations.

Introduce `z hz`. Establish `hz' : z ^ N = 1` using `hz`. Simplify `hz'` using `[Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)]`. Establish `: Finite S` using `hS.to_subtype`. Establish `: FiniteDimensional ℚ (IntermediateField.adjoin ℚ S)` using `IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral`.

Use `Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)` and prove the remaining obligations. Introduce `s hs`. Rewrite using `[MonoidHom.mem_ker]`. Use `hψ s ?_` and prove the remaining obligations. Introduce `z hz`.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z (IntermediateField.subset_adjoin ℚ S hz)`. Use `⟨hopen, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)), hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `h : ψ (x⁻¹ * y) = 1` using `hy`. Rewrite `h` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h.symm`.
-/
theorem isOpen_ker_and_isLocallyConstant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (C : Type) [Group C] (N : ℕ) (ψ : Formalism.ConjugateSelfDual.G ℚ Ω →* C) (hN : N ≠ 0)
    (hψ : UpperTheory.V.Af.KillsMu N ψ) :
    IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) ∧
      IsLocallyConstant (⇑ψ : Formalism.ConjugateSelfDual.G ℚ Ω → C) := by
  classical
  have hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let S : Set Ω := {z | z ^ N = 1}
    have hS : S.Finite := by
      refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_
      intro z hz
      have hz' : z ^ N = 1 := hz
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using hz'
    have : Finite S := hS.to_subtype
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro s hs
    rw [MonoidHom.mem_ker]
    refine hψ s ?_
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
      (IntermediateField.subset_adjoin ℚ S hz)
  refine ⟨hopen, ?_⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)),
    hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have h : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

end GlobalTheory.OpenKernelLocallyConstant
