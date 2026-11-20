import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

/- English proof (translation)
Use `⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩` and prove the remaining obligations. Establish `hx : algebraMap A K (x : A) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2`. Rewrite using `[Module.End.isUnit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `v w hvw`.

Establish `h' : (x : A) • v = (x : A) • w`. Simplify `hvw` using `[Module.algebraMap_end_apply]`. Rewrite `h'` using `[← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w]`. Conclude with `smul_right_injective Ω hx h'`. Introduce `v`.

Use `⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul, mul_inv_cancel₀ hx, one_smul]`. Establish `hy : y ∈ Submodule.span K (M : Set Ω)` using `hM ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩`.

Consider the case `zero => exact ⟨(0, 1), by simp⟩`. Consider the case `add y₁ y₂ _ _ h₁ h₂`. Take `⟨⟨m₁, s₁⟩, e₁⟩` from `h₁`. Take `⟨⟨m₂, s₂⟩, e₂⟩` from `h₂`. Use `⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩` and prove the remaining obligations.

Establish `e₁' : (s₁ : A) • y₁ = (m₁ : Ω)` using `e₁`. Establish `e₂' : (s₂ : A) • y₂ = (m₂ : Ω)` using `e₂`. Simplify using `only [map_add, map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def, Submonoid.coe_mul]`. Rewrite using `[smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁, smul_comm (s₂ : A) (s₁ : A) y₂]`. Consider the case `smul c z _ h`.

Take `⟨⟨m, s⟩, e⟩` from `h`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors A) c`. Simplify using `only at hab`. Establish `e' : (s : A) • z = (m : Ω)` using `e`. Establish `hb : (b : A) • (c • z) = a • z`.

Rewrite using `[← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]`. Use `⟨(a • m, b * s), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul, mul_comm, mul_smul, hb]`. Conclude with `smul_comm _ _ _`.
-/
theorem isLocalizedModule_subtype {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    IsLocalizedModule (nonZeroDivisors A) M.subtype := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩
  · have hx : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro v w hvw
      have h' : (x : A) • v = (x : A) • w := by
        simpa [Module.algebraMap_end_apply] using hvw
      rw [← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w] at h'
      exact smul_right_injective Ω hx h'
    · intro v
      refine ⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · have hy : y ∈ Submodule.span K (M : Set Ω) := hM ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨⟨m₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨m₂, s₂⟩, e₂⟩ := h₂
      refine ⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩
      have e₁' : (s₁ : A) • y₁ = (m₁ : Ω) := e₁
      have e₂' : (s₂ : A) • y₂ = (m₂ : Ω) := e₂
      simp only [map_add, map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def,
        Submonoid.coe_mul]
      rw [smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁,
        smul_comm (s₂ : A) (s₁ : A) y₂]
    | smul c z _ h =>
      obtain ⟨⟨m, s⟩, e⟩ := h
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
      dsimp only at hab
      have e' : (s : A) • z = (m : Ω) := e
      have hb : (b : A) • (c • z) = a • z := by
        rw [← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]
      refine ⟨(a • m, b * s), ?_⟩
      rw [map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul,
        mul_comm, mul_smul, hb]
      exact smul_comm _ _ _

/- English proof (translation)
Use `haveI := isLocalizedModule_subtype M hM`. Rewrite using `[IsFractionRing.finrank_right_eq A K Ω]`. Conclude with `IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl`.
-/
theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    finrank K Ω = finrank A M := by
  haveI := isLocalizedModule_subtype M hM
  rw [IsFractionRing.finrank_right_eq A K Ω]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl

/- English proof (translation)
Unfold `Module.rankAtStalk`. Rewrite using `[IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors]`. Conclude with `IsLocalizedModule.finrank_eq q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors`.
-/
private theorem rankAtStalk_eq_finrank' {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P]
    [Module R P] (q : PrimeSpectrum R) : Module.rankAtStalk P q = Module.finrank R P := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors

/- English proof (translation)
Introduce `A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hproj hL hspan hdim`. Use `haveI : IsDomain O := hv.hom_inj.isDomain`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : IsFractionRing O C := hv.isFractionRing`. Use `haveI : Module.Finite A M := Module.Finite.iff_fg.mpr hM.1`.

Use `haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1`. Use `haveI : Module.Flat O L := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `x ⟨a, ha⟩`. Rewrite using `[Submodule.mem_bot]`.

Establish `ha' : (a : O) • (x : Ω') = 0`. Use `congrArg Subtype.val ha` as an intermediate fact. Simplify `this` using `[Submonoid.smul_def]`. Rewrite `ha'` using `[← algebraMap_smul C (a : O)]`. Establish `hne : algebraMap O C (a : O) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2`.

Conclude with `Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)`. Use `letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)`. Use `haveI : IsScalarTower A O Ω' := ⟨fun a o x => by rw [Algebra.smul_def, mul_smul]; rfl⟩`. Set `ι' : M →ₗ[A] Ω'` to `{ toFun := ι, map_add' := map_add ι map_smul' := fun a x => by rw [LinearMap.map_smulₛₗ]; rfl }`. Set `j : O ⊗[A] M →ₗ[O] Ω'` to `ι'.liftBaseChange O`.

Establish `hj : ∀ x, j (1 ⊗ₜ x) = ι x` using `fun x => by show (1 : O) • ι x = ι x`. Conclude with `one_smul _ _`. Establish `hrange : LinearMap.range j = L`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, rfl⟩`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o x => show o • ι x ∈ L`. Conclude with `L.smul_mem o (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)`. Consider the case `add t₁ t₂ h₁ h₂ => rw [map_add]`.

Conclude with `L.add_mem h₁ h₂`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨1 ⊗ₜ x, hj x⟩`. Use `⟨j, ?_, hrange, hj⟩` and prove the remaining obligations.

Set `j' : O ⊗[A] M →ₗ[O] L` to `j.codRestrict L (fun t => hrange ▸ LinearMap.mem_range_self j t)`. Establish `hsurj : Function.Surjective j'`. Introduce and unpack `⟨y, hy⟩`. Rewrite `hy` using `[← hrange]`. Take `⟨t, rfl⟩` from `hy`.

Conclude with `⟨t, rfl⟩`. Establish `hbij : Function.Bijective j'`. Apply `Module.bijective_of_surjective_of_rankAtStalk_eq hsurj` to reduce the goal to its premises. Introduce `m _`. Rewrite using `[Module.rankAtStalk_baseChange, rankAtStalk_eq_finrank', rankAtStalk_eq_finrank', ← finrank_lattice M hM.2, hdim, finrank_lattice L hL.2]`.

Introduce `t₁ t₂ h`. Conclude with `hbij.1 (Subtype.ext h)`.
-/
theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsLattice K → Module.Projective A M → L.IsLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hproj hL hspan hdim
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite A M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    rw [Submodule.mem_bot]
    have ha' : (a : O) • (x : Ω') = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O)] at ha'
    have hne : algebraMap O C (a : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := ⟨fun a o x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ι' : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι
      map_smul' := fun a x => by rw [LinearMap.map_smulₛₗ]; rfl }
  let j : O ⊗[A] M →ₗ[O] Ω' := ι'.liftBaseChange O
  have hj : ∀ x, j (1 ⊗ₜ x) = ι x := fun x => by
    show (1 : O) • ι x = ι x
    exact one_smul _ _
  have hrange : LinearMap.range j = L := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul o x =>
        show o • ι x ∈ L
        exact L.smul_mem o (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
      | add t₁ t₂ h₁ h₂ => rw [map_add]; exact L.add_mem h₁ h₂
    · rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hj x⟩
  refine ⟨j, ?_, hrange, hj⟩
  let j' : O ⊗[A] M →ₗ[O] L := j.codRestrict L (fun t => hrange ▸ LinearMap.mem_range_self j t)
  have hsurj : Function.Surjective j' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hbij : Function.Bijective j' := by
    apply Module.bijective_of_surjective_of_rankAtStalk_eq hsurj
    intro m _
    rw [Module.rankAtStalk_baseChange, rankAtStalk_eq_finrank', rankAtStalk_eq_finrank', ← finrank_lattice M hM.2, hdim,
      finrank_lattice L hL.2]
  intro t₁ t₂ h
  exact hbij.1 (Subtype.ext h)

end PositivityTheory.HtPt.Gc
