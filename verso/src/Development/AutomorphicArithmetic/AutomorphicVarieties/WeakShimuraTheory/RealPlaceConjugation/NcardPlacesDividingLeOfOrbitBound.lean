import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
