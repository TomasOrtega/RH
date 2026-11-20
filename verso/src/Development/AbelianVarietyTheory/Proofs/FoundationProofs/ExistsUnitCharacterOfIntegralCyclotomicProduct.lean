import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

/- English proof (translation)
Introduce `l _ Ω _ _ c A k k' hcont hint hmul`. Establish `heps : ∀ s : G ℚ Ω, eps l s * algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Introduce `s`. Establish `h1 : algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (((cycBar ℚ Ω l s)⁻¹ : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[← map_inv]`.

Simplify using `[cycBar, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]`. Both sides reduce to the same expression. Rewrite using `[h1, eps]`. Conclude with `Units.mul_inv _`. Establish `hmem : ∀ s : G ℚ Ω, algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O` using `fun s => c.O.algebraMap_mem _`.

Set `f : ↥(Dec (F` to `ℚ) A) → c.Oˣ := fun g => Units.mkOfMulEqOne ⟨k g, (hint g g.2).1⟩ (⟨k' g, (hint g g.2).2.1⟩ * ⟨_, hmem g⟩) (by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one]`. Rewrite using `[← mul_assoc, (hint g g.2).2.2]`. Conclude with `heps g)`.

Establish `hf : ∀ g, (((f g : c.Oˣ) : c.O) : Qbar l) = k g` using `fun g => rfl`. Establish `hone : k 1 = 1`. Establish `h11` using `hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)`. Rewrite `h11` using `[one_mul]`. Establish `hu : IsUnit (((f 1 : c.Oˣ) : c.O) : Qbar l)`.

Establish `: IsUnit ((f 1 : c.Oˣ) : c.O)` using `Units.isUnit _`. Conclude with `this.map c.O.val`. Rewrite `hu` using `[hf, OneMemClass.coe_one]`. Conclude with `hu.mul_left_cancel (by rw [mul_one]; exact h11.symm)`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, hf⟩` and prove the remaining obligations.

Use `ext`. Express the relevant statement in the definitionally equal form `k _ = 1`. Rewrite using `[OneMemClass.coe_one, hone]`. Introduce `g h`. Use `ext`.

Express the relevant statement in the definitionally equal form `k _ = k _ * k _`. Rewrite using `[Subgroup.coe_mul]`. Conclude with `hmul g g.2 h h.2`. Establish `hc : Continuous ((Dec (F` using `ℚ) A : Set (G ℚ Ω)).restrict k) := continuousOn_iff_continuous_restrict.mp hcont`. Conclude with `hc.subtype_mk (fun g => (hint g g.2).1)`.
-/
theorem GlobalTheory.LocChar.unit_of_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  intro l _ Ω _ _ c A k k' hcont hint hmul

  have heps : ∀ s : G ℚ Ω, eps l s * algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro s
    have h1 : algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (((cycBar ℚ Ω l s)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← map_inv]
      simp [cycBar, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    rw [h1, eps]
    exact Units.mul_inv _
  have hmem : ∀ s : G ℚ Ω, algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O :=
    fun s => c.O.algebraMap_mem _
  let f : ↥(Dec (F := ℚ) A) → c.Oˣ := fun g =>
    Units.mkOfMulEqOne ⟨k g, (hint g g.2).1⟩
      (⟨k' g, (hint g g.2).2.1⟩ * ⟨_, hmem g⟩) (by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← mul_assoc, (hint g g.2).2.2]
        exact heps g)
  have hf : ∀ g, (((f g : c.Oˣ) : c.O) : Qbar l) = k g := fun g => rfl
  have hone : k 1 = 1 := by
    have h11 := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h11
    have hu : IsUnit (((f 1 : c.Oˣ) : c.O) : Qbar l) := by
      have : IsUnit ((f 1 : c.Oˣ) : c.O) := Units.isUnit _
      exact this.map c.O.val
    rw [hf, OneMemClass.coe_one] at hu
    exact hu.mul_left_cancel (by rw [mul_one]; exact h11.symm)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, hf⟩
  · ext
    change k _ = 1
    rw [OneMemClass.coe_one, hone]
  · intro g h
    ext
    change k _ = k _ * k _
    rw [Subgroup.coe_mul]
    exact hmul g g.2 h h.2
  · have hc : Continuous ((Dec (F := ℚ) A : Set (G ℚ Ω)).restrict k) :=
      continuousOn_iff_continuous_restrict.mp hcont
    exact hc.subtype_mk (fun g => (hint g g.2).1)
