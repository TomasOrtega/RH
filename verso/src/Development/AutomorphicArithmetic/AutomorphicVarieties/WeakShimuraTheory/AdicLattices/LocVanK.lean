import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

/- English proof (translation)
Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lvk_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases h1 : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]
    intro φ
    obtain ⟨m, hm⟩ := h φ
    rw [hm, h1, one_mul, sub_self]
  · obtain ⟨g₀, hg₀⟩ := not_forall.mp h1
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.mpr hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]
    intro φ
    obtain ⟨m, hm⟩ := h φ
    simp only [map_sub, map_smul, hm, smul_eq_mul]
    field_simp
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.Lat.locVanK :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → UpperTheory.V.Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) →
      ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ p ∈ D.Sb, ∀ z : D.Gp p → k, IsLocallyConstant z →
      (∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) → ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD hP k _ red hred γ hγ p hp z hlc hco
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  let f : ResidueField c.O →+* k := Ideal.Quotient.lift (maximalIdeal c.O) red hred
  letI : Algebra (ResidueField c.O) k := f.toAlgebra
  have hf : ∀ a : c.O, algebraMap (ResidueField c.O) k (residue c.O a) = red a := fun a => rfl
  have hs : ∀ (a : c.O) (x : k), red a * x = residue c.O a • x := fun a x => by
    rw [Algebra.smul_def, hf]
  have key := lvk_coord (fun g : D.Gp p => residue c.O (γ g : c.O)) z fun φ =>
    UpperTheory.V.GradeZeroInterpolatingElement.locVanP D hD hP (ResidueField c.O) (residue c.O)
      (fun a ha => (residue_eq_zero_iff a).2 ha) γ hγ p hp (fun g => φ (z g)) (hlc.comp φ) fun g h => by
        simp only [hco, hs, map_add, map_smul, smul_eq_mul]
  simpa only [hf] using key
