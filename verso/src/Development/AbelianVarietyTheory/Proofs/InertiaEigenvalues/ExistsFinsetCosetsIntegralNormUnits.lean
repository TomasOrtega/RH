import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NormUnits

/- English proof (translation)
Introduce `K B hP` and use `haveI := GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra K (GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext K) B.A (GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP)`.
-/
theorem fg_quot_intUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := fun K B hP =>
  haveI := GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP
  GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra K (GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext K) B.A (GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP)

/- English proof (translation)
Set `M` to `Additive (G ⧸ N)`. Use `haveI : AddGroup.FG M := inferInstance`. Use `haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance`. Set `K2 : Submodule ℤ M` to `LinearMap.ker (LinearMap.lsmul ℤ M 2)`. Use `haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2`.

Use `haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `x.2`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.lsmul_apply]`. Simplify using `using h⟩)`.

Set `r : K2 → G` to `fun k => Quotient.out (Additive.toMul (k : M))`. Use `⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2` using `by show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0`. Rewrite using `[← ofMul_zpow]`. Use `show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1`.

Use `congr 1`. Rewrite using `[zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]`. Conclude with `hu`. Use `⟨r ⟨_, hk⟩, by simp, ?_⟩` and prove the remaining obligations. Establish `h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u`.

Simplify using `only [r]`. Conclude with `Quotient.out_eq' _`. Use `QuotientGroup.eq.mp h1.symm` as an intermediate fact. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]`.
-/
theorem exists_finset_sq_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by
  let M := Additive (G ⧸ N)
  haveI : AddGroup.FG M := inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let K2 : Submodule ℤ M := LinearMap.ker (LinearMap.lsmul ℤ M 2)
  haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2
  haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by
    apply Subtype.ext; have h := x.2; rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at h
    simpa using h⟩)
  let r : K2 → G := fun k => Quotient.out (Additive.toMul (k : M))
  refine ⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩
  have hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2 := by
    show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0
    rw [← ofMul_zpow]
    show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1
    congr 1
    rw [zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]; exact hu
  refine ⟨r ⟨_, hk⟩, by simp, ?_⟩
  have h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u := by
    simp only [r]; exact Quotient.out_eq' _
  have := QuotientGroup.eq.mp h1.symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

/- English proof (translation)
Introduce `K B hP`. Set `N : Subgroup B.Aˣ` to `B.T ⊔ intUnits K.O B.A`. Establish `hFG : Group.FG (B.Aˣ ⧸ N)` using `haveI := fg_quot_intUnits K B hP Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right) (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)`. Take `⟨F, hF⟩` from `exists_finset_sq_mem N hFG`. Use `⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩` and prove the remaining obligations.

Set `su : B.Aˣ` to `Units.map (B.σ : B.A →* B.A) u`. Establish `hsu : (su : B.A) = B.σ u` using `rfl`. Establish `ht : u * su⁻¹ ∈ B.T` using `by show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1`. Establish `h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1`. Establish `: B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`.

Rewrite `this` using `[hsu, B.σ_σ]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, map_mul]`. Rewrite using `[hsu]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 1 := by rw [h1, Units.mul_inv, one_mul]`. Establish `hsq : u ^ 2 ∈ N`. Establish `: u ^ 2 = (u * su⁻¹) * w` using `by ext; rw [Units.val_mul, hwu, ← hsu]`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[this]`. Conclude with `N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)`. Take `⟨f, hfF, hf⟩` from `hF u hsq`. Take `⟨t, htT, z, hz, htz⟩` from `Subgroup.mem_sup.mp hf`. Use `⟨f, hfF, t, htT, ?_⟩` and prove the remaining obligations.

Establish `: u * f⁻¹ * t⁻¹ = z` using `by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]`. Rewrite using `[this]`. Conclude with `hz`.
-/
theorem exists_finset_normUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ,
    (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  intro K B hP
  let N : Subgroup B.Aˣ := B.T ⊔ intUnits K.O B.A
  have hFG : Group.FG (B.Aˣ ⧸ N) :=
    haveI := fg_quot_intUnits K B hP
    Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right)
      (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)
  obtain ⟨F, hF⟩ := exists_finset_sq_mem N hFG
  refine ⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩
  let su : B.Aˣ := Units.map (B.σ : B.A →* B.A) u
  have hsu : (su : B.A) = B.σ u := rfl
  have ht : u * su⁻¹ ∈ B.T := by
    show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1
    have h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1 := by
      have : B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rwa [hsu, B.σ_σ] at this
    calc ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A)
        = (B.σ ((su⁻¹ : B.Aˣ) : B.A) * u) * ((su : B.A) * ((su⁻¹ : B.Aˣ) : B.A)) := by
          simp only [Units.val_mul, map_mul]; rw [hsu]; ring
      _ = 1 := by rw [h1, Units.mul_inv, one_mul]
  have hsq : u ^ 2 ∈ N := by
    have : u ^ 2 = (u * su⁻¹) * w := by
      ext; rw [Units.val_mul, hwu, ← hsu]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul]
      calc (u : B.A) ^ 2 = (u : B.A) * u * (((su⁻¹ : B.Aˣ) : B.A) * su) := by rw [Units.inv_mul, mul_one, sq]
        _ = _ := by ring
    rw [this]; exact N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)
  obtain ⟨f, hfF, hf⟩ := hF u hsq
  obtain ⟨t, htT, z, hz, htz⟩ := Subgroup.mem_sup.mp hf
  refine ⟨f, hfF, t, htT, ?_⟩
  have : u * f⁻¹ * t⁻¹ = z := by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]; exact hz

end GlobalTheory.NormUnits
