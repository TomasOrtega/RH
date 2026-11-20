import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToZModPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaClosed

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Establish `hH : ((IntermediateField.adjoin ℚ {x}).fixingSubgroup : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω)` using `(IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `σ hσ`. Rewrite using `[← map_mul_left_nhds_one σ]`.

Use `Filter.mem_map.2 (Filter.mem_of_superset hH fun τ hτ => ?_)` and prove the remaining obligations. Establish `hτx : τ x = x` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self ℚ x)`. Use `show P ((σ * τ) x)`. Rewrite using `[AlgEquiv.mul_apply, hτx]`. Conclude with `hσ`.
-/
theorem isOpen_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsOpen {σ : G ℚ Ω | P (σ x)} := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hH : ((IntermediateField.adjoin ℚ {x}).fixingSubgroup : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  rw [← map_mul_left_nhds_one σ]
  refine Filter.mem_map.2 (Filter.mem_of_superset hH fun τ hτ => ?_)
  have hτx : τ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self ℚ x)
  show P ((σ * τ) x)
  rw [AlgEquiv.mul_apply, hτx]
  exact hσ

/- English proof (translation)
Establish `h` using `isOpen_setOf_apply x (fun y => ¬ P y)`. Rewrite using `[← isOpen_compl_iff]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `σ`. Simplify using the standard rewrite rules.
-/
theorem isClosed_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {σ : G ℚ Ω | P (σ x)} := by
  have h := isOpen_setOf_apply x (fun y => ¬ P y)
  rw [← isOpen_compl_iff]
  convert h using 1
  ext σ; simp

/- English proof (translation)
Use `show σ ∈ Dec (F := ℚ) A`. Rewrite using `[mem_Dec]`. Use extensionality with `x`. Rewrite using `[show x = σ ((σ⁻¹ : G ℚ Ω) x) from (mul_inv_apply x).symm, ← AlgEquiv.smul_def σ ((σ⁻¹ : G ℚ Ω) x), ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, h]`.
-/
theorem mem_dec_of_forall {A : ValuationSubring Ω} {σ : G ℚ Ω} (h : ∀ x, σ x ∈ A ↔ x ∈ A) :
    σ ∈ A.decompositionSubgroup ℚ := by
  show σ ∈ Dec (F := ℚ) A
  rw [mem_Dec]
  ext x
  rw [show x = σ ((σ⁻¹ : G ℚ Ω) x) from (mul_inv_apply x).symm, ← AlgEquiv.smul_def σ ((σ⁻¹ : G ℚ Ω) x),
    ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, h]

/- English proof (translation)
Establish `e : ((Ine (F` using `ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) = (⋂ x : Ω, {σ : G ℚ Ω | (σ x ∈ A ↔ x ∈ A)}) ∩ ⋂ x : Ω, {σ : G ℚ Ω | A.valuation x ≤ 1 → A.valuation (σ x - x) < 1} := by`. Use extensionality with `σ`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨fun x => apply_mem_iff_of_mem_Dec (F := ℚ) h.1 x, h.2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨mem_dec_of_forall h1, h2⟩`. Rewrite using `[e]`. Conclude with `(isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => (y ∈ A ↔ x ∈ A))).inter (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))`.
-/
theorem isClosed_Ine [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) :
    IsClosed ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have e : ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (⋂ x : Ω, {σ : G ℚ Ω | (σ x ∈ A ↔ x ∈ A)}) ∩
        ⋂ x : Ω, {σ : G ℚ Ω | A.valuation x ≤ 1 → A.valuation (σ x - x) < 1} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun x => apply_mem_iff_of_mem_Dec (F := ℚ) h.1 x, h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mem_dec_of_forall h1, h2⟩
  rw [e]
  exact (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => (y ∈ A ↔ x ∈ A))).inter
    (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x
      (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ContinuousZModPow.main`. Consider the case `exact _root_.GlobalTheory.ContinuousZModPow.main`. Consider the case `(apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ContinuousZModPow.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ContinuousZModPow.main ..)`.
-/
theorem continuous_toZModPow' (l : ℕ) [hl : Fact l.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) n) := by
  first
  | exact @_root_.GlobalTheory.ContinuousZModPow.main
  | exact _root_.GlobalTheory.ContinuousZModPow.main
  | (apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousZModPow.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousZModPow.main ..)

/- English proof (translation)
Establish `hc : Continuous fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])` using `(continuous_toZModPow' l m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))`. Establish `e : (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) = (fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' {1}`. Use extensionality with `σ`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]`. Rewrite using `[← Units.val_eq_one]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(isClosed_discrete _).preimage hc`.
-/
theorem isClosed_ker_cycMod (l : ℕ) [Fact l.Prime] (m : ℕ) :
    IsClosed (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have hc : Continuous fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) :=
    (continuous_toZModPow' l m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
  have e : (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' {1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Units.val_eq_one]
    rfl
  rw [e]
  exact (isClosed_discrete _).preimage hc

end GlobalTheory.InertiaClosed

open GlobalTheory.InertiaClosed in

/- English proof (translation)
Introduce `l _ Ω _ _ _ A m`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `(isClosed_Ine A).inter (isClosed_ker_cycMod l m)`.
-/
theorem GlobalTheory.isClosed_Ine_inf_ker_cycMod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ),
    IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  intro l _ Ω _ _ _ A m
  rw [Subgroup.coe_inf]
  exact (isClosed_Ine A).inter (isClosed_ker_cycMod l m)
