import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.fzkLaw : UpperTheory.V.Z.Sym.Loc.FzkLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  have inj : Function.Injective (algebraMap O K) := by
    haveI := hL.frac
    exact IsFractionRing.injective O K
  have ent : ∀ b : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = b := by
    intro b
    simp
  have key : ∀ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ KG O K → χ a = 1 := by
    rintro a ⟨M, hM⟩
    have a1 : algebraMap O K ((M : Matrix (Fin 2) (Fin 2) O) 0 0) = (a : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM
      exact this.trans (ent a)
    have hM' : Matrix.GeneralLinearGroup.map (algebraMap O K) M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by
      rw [map_inv, hM, map_inv]
    have a2 : algebraMap O K (((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0) = ((a⁻¹ : Kˣ) : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM'
      exact this.trans (ent a⁻¹)
    have hp : (M : Matrix (Fin 2) (Fin 2) O) 0 0 * ((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0 = 1 := by
      apply inj
      rw [map_mul, a1, a2, Units.mul_inv, map_one]
    have hu : Units.map (algebraMap O K : O →* K) (Units.mkOfMulEqOne _ _ hp) = a := by
      ext
      simpa using a1
    rw [← hu]
    exact hχ _
  refine ⟨fun g hg => ?_, fun z k hk => ?_⟩
  · unfold fZK
    rw [dif_neg]
    rintro ⟨z, hz⟩
    apply hg
    rw [← mul_inv_cancel_left (Matrix.GeneralLinearGroup.scalar (Fin 2) z) g]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨z, rfl⟩) (Subgroup.mem_sup_right hz)
  · have hex : ∃ w, (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) ∈ KG O K :=
      ⟨z, by rw [inv_mul_cancel_left]; exact hk⟩
    unfold fZK
    rw [dif_pos hex]
    have hw := hex.choose_spec
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) ∈ KG O K := by
      have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) = (Matrix.GeneralLinearGroup.scalar (Fin 2) hex.choose)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) * k⁻¹ := by
        rw [map_mul, map_inv]
        simp [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hk)
    have h1 := key _ hs
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1]
