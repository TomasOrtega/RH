import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`. Establish `h2` using `ValuationSubring.smul_mem_pointwise_smul e x A hx`. Use `open Pointwise in`. Establish `h3 : e • A = A` using `he`. Rewrite `h2` using `[h3]`.

Conclude with `h2`.
-/
private theorem valuation_apply_le_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (x : Ω) (hx : A.valuation x ≤ 1) : A.valuation (e x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  have h2 := ValuationSubring.smul_mem_pointwise_smul e x A hx
  open Pointwise in
  have h3 : e • A = A := he
  rw [h3] at h2
  exact h2

/- English proof (translation)
Break down `eq_or_ne z 0 with rfl | hz0` into its components or cases. Simplify using `using hz`. Establish `hez : e z ≠ 0` using `by simpa using hz0`. Establish `key : 1 < A.valuation z⁻¹`. Rewrite using `[Valuation.one_lt_val_iff _ (inv_ne_zero hz0), inv_inv]`.

Conclude with `hz`. Establish `h1 : 1 < A.valuation (e z)⁻¹`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4` using `valuation_apply_le_one_of_mem_dec A e⁻¹ (inv_mem he) _ hc`.

Establish `h5 : e⁻¹ (e z)⁻¹ = z⁻¹`. Rewrite using `[map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Rewrite `h4` using `[h5]`. Conclude with `absurd key (not_lt.mpr h4)`. Rewrite `h1` using `[Valuation.one_lt_val_iff _ (inv_ne_zero hez), inv_inv]`.

Conclude with `h1`.
-/
private theorem valuation_apply_lt_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (z : Ω) (hz : A.valuation z < 1) : A.valuation (e z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  have hez : e z ≠ 0 := by simpa using hz0
  have key : 1 < A.valuation z⁻¹ := by
    rw [Valuation.one_lt_val_iff _ (inv_ne_zero hz0), inv_inv]
    exact hz
  have h1 : 1 < A.valuation (e z)⁻¹ := by
    by_contra hc
    push_neg at hc
    have h4 := valuation_apply_le_one_of_mem_dec A e⁻¹ (inv_mem he) _ hc
    have h5 : e⁻¹ (e z)⁻¹ = z⁻¹ := by
      rw [map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [h5] at h4
    exact absurd key (not_lt.mpr h4)
  rw [Valuation.one_lt_val_iff _ (inv_ne_zero hez), inv_inv] at h1
  exact h1

/- English proof (translation)
Establish `hτD : τ ∈ Dec A` using `Ine_le_Dec A hτ`. Take `⟨_, hτ2⟩` from `hτ`. Use `⟨(Dec A).mul_mem ((Dec A).mul_mem ((Dec A).inv_mem hd) hτD) hd, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hτ2 (d x) (valuation_apply_le_one_of_mem_dec A d hd x hx)`. Establish `h2` using `valuation_apply_lt_one_of_mem_dec A d⁻¹ ((Dec A).inv_mem hd) _ h1`.

Establish `e : (d⁻¹ * τ * d) x - x = d⁻¹ (τ (d x) - d x)`. Rewrite using `[map_sub, ← AlgEquiv.mul_apply d⁻¹ d, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply]`. Rewrite using `[e]`. Conclude with `h2`.
-/
private theorem inv_mul_mul_mem_ine_of_mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (d τ : G F Ω) (hd : d ∈ Dec A) (hτ : τ ∈ Ine A) :
    d⁻¹ * τ * d ∈ Ine A := by
  have hτD : τ ∈ Dec A := Ine_le_Dec A hτ
  obtain ⟨_, hτ2⟩ := hτ
  refine ⟨(Dec A).mul_mem ((Dec A).mul_mem ((Dec A).inv_mem hd) hτD) hd, fun x hx => ?_⟩
  have h1 := hτ2 (d x) (valuation_apply_le_one_of_mem_dec A d hd x hx)
  have h2 := valuation_apply_lt_one_of_mem_dec A d⁻¹ ((Dec A).inv_mem hd) _ h1
  have e : (d⁻¹ * τ * d) x - x = d⁻¹ (τ (d x) - d x) := by
    rw [map_sub, ← AlgEquiv.mul_apply d⁻¹ d, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply]
  rw [e]
  exact h2

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ A v hAv φ hφ X hX hXI g hg`. Use `set Y : Set Ω := {y | ∀ τ ∈ Ine (F := F) A, τ y = y} with hYdef`. Establish `hφD : φ ∈ Dec A` using `hφ.1`. Establish `hstab : ∀ (k : ℤ) (y : Ω), y ∈ Y → (φ ^ k) y ∈ Y`. Introduce `k y hy τ hτ`.

Establish `h1` using `hy _ (inv_mul_mul_mem_ine_of_mem_dec A (φ ^ k) τ (zpow_mem hφD k) hτ)`. Establish `h2` using `congrArg (φ ^ k) h1`. Rewrite `h2` using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ k) (φ ^ k)⁻¹, mul_inv_cancel, AlgEquiv.one_apply]`. Conclude with `h2`. Set `φ' : Dec A` to `⟨φ, hφD⟩`.

Establish `hdense` using `GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hAv φ' hφ`. Establish `hP : ∀ h ∈ (Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)), ∃ k : ℤ, ∀ y ∈ Y, (h : G F Ω) y = (φ ^ k) y`. Introduce `h hh`. Rewrite `hh` using `[Subgroup.sup_eq_closure]`. Proceed by induction on `hh using Subgroup.closure_induction with`.

Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hx`. Conclude with `⟨k, fun y _ => by rw [Subgroup.coe_zpow]⟩`. Use `⟨0, fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_zero, AlgEquiv.one_apply]`. Conclude with `hy _ (Subgroup.mem_subgroupOf.mp hx)`. Consider the case `one => exact ⟨0, fun y _ => by rw [zpow_zero]; rfl⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Use `⟨a + b, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, AlgEquiv.mul_apply, hb z hz, ha _ (hstab b z hz), zpow_add, AlgEquiv.mul_apply]`. Consider the case `inv x _ hx`. Take `⟨a, ha⟩` from `hx`.

Use `⟨-a, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hw` using `ha _ (hstab (-a) z hz)`. Establish `e1 : (φ ^ a) ((φ ^ (-a)) z) = z`. Rewrite using `[← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]`. Rewrite `hw` using `[e1]`.

Rewrite using `[Subgroup.coe_inv]`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic`. Use `haveI : Finite X := hX.to_subtype`. Use `haveI : FiniteDimensional F (IntermediateField.adjoin F X) := IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)`.

Set `O : Set (Dec A)` to `Subtype.val ⁻¹' ((fun σ : G F Ω => g⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F X).fixingSubgroup : Set (G F Ω)))`. Establish `hO : IsOpen O` using `((IntermediateField.adjoin F X).fixingSubgroup_isOpen.preimage (continuous_mul_left g⁻¹)).preimage continuous_subtype_val`. Establish `hgO : (⟨g, hg⟩ : Dec A) ∈ O` using `by show g⁻¹ * g ∈ (IntermediateField.adjoin F X).fixingSubgroup`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`.

Establish `hmem : (⟨g, hg⟩ : Dec A) ∈ ((Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)).topologicalClosure : Set (Dec A))`. Rewrite using `[hdense]`. Conclude with `Subgroup.mem_top _`. Rewrite `hmem` using `[Subgroup.topologicalClosure_coe]`. Take `⟨h, hhO, hhK⟩` from `(mem_closure_iff.mp hmem) O hO hgO`.

Take `⟨k, hk⟩` from `hP h hhK`. Use `⟨k, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hfix : g⁻¹ * (h : G F Ω) ∈ (IntermediateField.adjoin F X).fixingSubgroup` using `hhO`. Establish `h1` using `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x (IntermediateField.subset_adjoin F X hx)`. Establish `hxY : x ∈ Y` using `fun τ hτ => hXI τ hτ x hx`.

Rewrite using `[← hk x hxY]`. Establish `h2` using `congrArg g h1`. Rewrite `h2` using `[AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply]`. Conclude with `h2.symm`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.decGen :
    DecGen := by
  intro F Ω _ _ _ _ _ A v hAv φ hφ X hX hXI g hg
  set Y : Set Ω := {y | ∀ τ ∈ Ine (F := F) A, τ y = y} with hYdef
  have hφD : φ ∈ Dec A := hφ.1
  have hstab : ∀ (k : ℤ) (y : Ω), y ∈ Y → (φ ^ k) y ∈ Y := by
    intro k y hy τ hτ
    have h1 := hy _ (inv_mul_mul_mem_ine_of_mem_dec A (φ ^ k) τ (zpow_mem hφD k) hτ)
    have h2 := congrArg (φ ^ k) h1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ k) (φ ^ k)⁻¹,
      mul_inv_cancel, AlgEquiv.one_apply] at h2
    exact h2
  let φ' : Dec A := ⟨φ, hφD⟩
  have hdense := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hAv φ' hφ
  have hP : ∀ h ∈ (Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)),
      ∃ k : ℤ, ∀ y ∈ Y, (h : G F Ω) y = (φ ^ k) y := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨k, fun y _ => by rw [Subgroup.coe_zpow]⟩
      · refine ⟨0, fun y hy => ?_⟩
        rw [zpow_zero, AlgEquiv.one_apply]
        exact hy _ (Subgroup.mem_subgroupOf.mp hx)
    | one => exact ⟨0, fun y _ => by rw [zpow_zero]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, fun z hz => ?_⟩
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb z hz, ha _ (hstab b z hz), zpow_add,
        AlgEquiv.mul_apply]
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨-a, fun z hz => ?_⟩
      have hw := ha _ (hstab (-a) z hz)
      have e1 : (φ ^ a) ((φ ^ (-a)) z) = z := by
        rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]
      rw [e1] at hw
      rw [Subgroup.coe_inv]
      calc ((x : G F Ω)⁻¹) z = ((x : G F Ω)⁻¹) ((x : G F Ω) ((φ ^ (-a)) z)) := by rw [hw]
        _ = (φ ^ (-a)) z := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Finite X := hX.to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F X) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let O : Set (Dec A) := Subtype.val ⁻¹' ((fun σ : G F Ω => g⁻¹ * σ) ⁻¹'
    ((IntermediateField.adjoin F X).fixingSubgroup : Set (G F Ω)))
  have hO : IsOpen O :=
    ((IntermediateField.adjoin F X).fixingSubgroup_isOpen.preimage (continuous_mul_left g⁻¹)).preimage
      continuous_subtype_val
  have hgO : (⟨g, hg⟩ : Dec A) ∈ O := by
    show g⁻¹ * g ∈ (IntermediateField.adjoin F X).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  have hmem : (⟨g, hg⟩ : Dec A) ∈
      ((Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)).topologicalClosure : Set (Dec A)) := by
    rw [hdense]
    exact Subgroup.mem_top _
  rw [Subgroup.topologicalClosure_coe] at hmem
  obtain ⟨h, hhO, hhK⟩ := (mem_closure_iff.mp hmem) O hO hgO
  obtain ⟨k, hk⟩ := hP h hhK
  refine ⟨k, fun x hx => ?_⟩
  have hfix : g⁻¹ * (h : G F Ω) ∈ (IntermediateField.adjoin F X).fixingSubgroup := hhO
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x
    (IntermediateField.subset_adjoin F X hx)
  have hxY : x ∈ Y := fun τ hτ => hXI τ hτ x hx
  rw [← hk x hxY]
  have h2 := congrArg g h1
  rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
  exact h2.symm
