import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

/- English proof (translation)
Distinguish the cases in `h1 : ∀ g, a g = 1`. Use `⟨0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, sub_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]`. Introduce `φ`. Take `⟨m, hm⟩` from `h φ`.

Rewrite using `[hm, h1, one_mul, sub_self]`. Take `⟨g₀, hg₀⟩` from `not_forall.mp h1`. Establish `hne : a g₀ - 1 ≠ 0` using `sub_ne_zero.mpr hg₀`. Use `⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]`.

Introduce `φ`. Take `⟨m, hm⟩` from `h φ`. Simplify using `only [map_sub, map_smul, hm, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `Ω _ _ _ l _ c D hD hP k _ red hred γ hγ p hp z hlc hco`. Use `haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1`. Set `f : ResidueField c.O →+* k` to `Ideal.Quotient.lift (maximalIdeal c.O) red hred`. Use `letI : Algebra (ResidueField c.O) k := f.toAlgebra`. Establish `hf : ∀ a : c.O, algebraMap (ResidueField c.O) k (residue c.O a) = red a` using `fun a => rfl`.

Establish `hs : ∀ (a : c.O) (x : k), red a * x = residue c.O a • x` using `fun a x => by`. Rewrite using `[Algebra.smul_def, hf]`. Establish `key` using `lvk_coord (fun g : D.Gp p => residue c.O (γ g : c.O)) z fun φ => UpperTheory.V.GradeZeroInterpolatingElement.locVanP D hD hP (ResidueField c.O) (residue c.O) (fun a ha => (residue_eq_zero_iff a).2 ha) γ hγ p hp (fun g => φ (z g)) (hlc.comp φ) fun g h => by`. Simplify using `only [hco, hs, map_add, map_smul, smul_eq_mul]`. Simplify `key` using `only [hf]`.
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
