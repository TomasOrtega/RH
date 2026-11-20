import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Trivial
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.FormationThree
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.NotDvdSuperIndexBotOfIsProPGroup
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.CdpOpenSubgroupLe
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
import GroundTheory.ProfiniteCohomology.CartierDual
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn h x hx`. Break down `eq_or_ne n 1 with rfl | h1` into its components or cases.

Rewrite `hx` using `[one_nsmul]`. Then use the resulting hypothesis. Use `set ℓ := n.minFac`. Establish `hℓ : ℓ.Prime` using `Nat.minFac_prime h1`. Take `⟨n', hn'⟩ : ℓ ∣ n` from `Nat.minFac_dvd n`. Establish `hn'0 : n' ≠ 0` using `fun h0 => hn (by rw [hn', h0, mul_zero])`.

Establish `hy : n' • x = 0`. Use `(primaryComponent_eq_bot_iff.1 (h ℓ hℓ ⟨n', hn'⟩)) (n' • x) ⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, smul_smul, ← hn', hx]`. Use `ih n' ?_ hn'0 (fun q hq hqn => h q hq (hqn.trans ⟨ℓ, by rw [hn', mul_comm]⟩)) x hy` and prove the remaining obligations. Rewrite using `[hn']`.

Conclude with `lt_mul_left (Nat.pos_of_ne_zero hn'0) hℓ.one_lt`.
-/
theorem eq_zero_of_primaryComponent_eq_bot {M : Type*} [AddCommGroup M] :
    ∀ (n : ℕ), n ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → AddCommGroup.primaryComponent M ℓ = ⊥) →
      ∀ x : M, n • x = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn h x hx
  rcases eq_or_ne n 1 with rfl | h1
  · rwa [one_nsmul] at hx
  set ℓ := n.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  obtain ⟨n', hn'⟩ : ℓ ∣ n := Nat.minFac_dvd n
  have hn'0 : n' ≠ 0 := fun h0 => hn (by rw [hn', h0, mul_zero])
  have hy : n' • x = 0 := by
    refine (primaryComponent_eq_bot_iff.1 (h ℓ hℓ ⟨n', hn'⟩)) (n' • x) ⟨1, ?_⟩
    rw [pow_one, smul_smul, ← hn', hx]
  refine ih n' ?_ hn'0 (fun q hq hqn => h q hq (hqn.trans ⟨ℓ, by rw [hn', mul_comm]⟩)) x hy
  rw [hn']
  exact lt_mul_left (Nat.pos_of_ne_zero hn'0) hℓ.one_lt

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/- English proof (translation)
The claim follows from `(localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_three U`.
-/
theorem subsingleton_cohomology_three_galUnits_open (U : OpenSubgroup Gal(Ksep/K)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) 3) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_three U

/- English proof (translation)
The claim follows from `subsingleton_cohomology_three_rootsOfUnity_open K Ksep hn U (subsingleton_cohomology_three_galUnits_open K Ksep U)`.
-/
theorem subsingleton_cohomology_three_rootsOfUnity {n : ℕ} (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 3) :=
  subsingleton_cohomology_three_rootsOfUnity_open K Ksep hn U
    (subsingleton_cohomology_three_galUnits_open K Ksep U)

end Local

section Sylow

attribute [local instance 2000] Rep.hV2

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `σ hσ τ`. Use `Subgroup.mem_iInf.2 fun x => ?_` and prove the remaining obligations. Establish `h1` using `Subgroup.mem_iInf.1 hσ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x)`. Express the relevant statement in the definitionally equal form `(galRootsOfUnity.{0} K Ksep n).ρ (τ * σ * τ⁻¹) x = x`.

Express the relevant statement in the definitionally equal form `(galRootsOfUnity.{0} K Ksep n).ρ σ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x) = (galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x at h1`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1, Representation.self_inv_apply]`.
-/
theorem rootsOfUnityFixing_normal (n : ℕ) [NeZero n] :
    ((rootsOfUnityFixing K Ksep n : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal := by
  constructor
  intro σ hσ τ
  refine Subgroup.mem_iInf.2 fun x => ?_
  have h1 := Subgroup.mem_iInf.1 hσ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x)
  change (galRootsOfUnity.{0} K Ksep n).ρ (τ * σ * τ⁻¹) x = x
  change (galRootsOfUnity.{0} K Ksep n).ρ σ ((galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x) =
    (galRootsOfUnity.{0} K Ksep n).ρ τ⁻¹ x at h1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1,
    Representation.self_inv_apply]

def rootsOfUnityFixingNormal (n : ℕ) [NeZero n] : OpenNormalSubgroup Gal(Ksep/K) :=
  { rootsOfUnityFixing K Ksep n with isNormal' := rootsOfUnityFixing_normal n }

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Establish `: NeZero ℓ` using `⟨hℓ.ne_zero⟩`. Set `W` to `rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) ℓ`. Establish `: ((rootsOfUnityFixing K Ksep ℓ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal` using `rootsOfUnityFixing_normal ℓ`. Take `⟨k, hk⟩` from `(isProPGroup_subgroup_iff_isPGroup_map.1 hP W) ⟨QuotientGroup.mk' (W : Subgroup Gal(Ksep/K)) σ, Subgroup.mem_map_of_mem _ hσ⟩`.

Establish `hmem : σ ^ ℓ ^ k ∈ rootsOfUnityFixing K Ksep ℓ`. Establish `h` using `congrArg Subtype.val hk`. Simplify using `only [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow] at h`. Conclude with `(QuotientGroup.eq_one_iff _).1 h`. Establish `hfixk : (σ ^ ℓ ^ k) ζ = ζ` using `apply_eq_of_mem_rootsOfUnityFixing hmem hζ`.

Establish `hu : IsUnit ζ` using `IsUnit.of_pow_eq_one hζ hℓ.ne_zero`. Take `⟨m, hm⟩` from `map_rootsOfUnity_eq_pow_self σ (⟨hu.unit, (mem_rootsOfUnity ℓ _).2 (Units.ext (by simpa using hζ))⟩ : rootsOfUnity ℓ Ksep)`. Establish `hm' : σ ζ = ζ ^ m` using `hm`. Establish `hpow : ∀ j : ℕ, (σ ^ j) ζ = ζ ^ (m ^ j)`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hm', ← pow_mul, ← pow_succ']`. Establish `hmodpow : ∀ a : ℕ, ζ ^ a = ζ ^ (a % ℓ)` using `fun a => by conv_lhs => rw [← Nat.mod_add_div a ℓ, pow_add, pow_mul, hζ, one_pow, mul_one]`. Establish `hmod : m ^ ℓ ^ k % ℓ = m % ℓ`.

Establish `h` using `ZMod.pow_card_pow (p := ℓ) (n := k) (m : ZMod ℓ)`. Rewrite `h` using `[← Nat.cast_pow]`. Conclude with `(ZMod.natCast_eq_natCast_iff' _ _ _).1 h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem apply_eq_of_isProPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) {P : Subgroup Gal(Ksep/K)}
    (hP : IsProPGroup ℓ P) {σ : Gal(Ksep/K)} (hσ : σ ∈ P) {ζ : Ksep} (hζ : ζ ^ ℓ = 1) : σ ζ = ζ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let W := rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) ℓ
  have : ((rootsOfUnityFixing K Ksep ℓ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal :=
    rootsOfUnityFixing_normal ℓ
  obtain ⟨k, hk⟩ := (isProPGroup_subgroup_iff_isPGroup_map.1 hP W)
    ⟨QuotientGroup.mk' (W : Subgroup Gal(Ksep/K)) σ, Subgroup.mem_map_of_mem _ hσ⟩
  have hmem : σ ^ ℓ ^ k ∈ rootsOfUnityFixing K Ksep ℓ := by
    have h := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hfixk : (σ ^ ℓ ^ k) ζ = ζ := apply_eq_of_mem_rootsOfUnityFixing hmem hζ
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ hℓ.ne_zero
  obtain ⟨m, hm⟩ := map_rootsOfUnity_eq_pow_self σ
    (⟨hu.unit, (mem_rootsOfUnity ℓ _).2 (Units.ext (by simpa using hζ))⟩ : rootsOfUnity ℓ Ksep)
  have hm' : σ ζ = ζ ^ m := hm
  have hpow : ∀ j : ℕ, (σ ^ j) ζ = ζ ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hm', ← pow_mul, ← pow_succ']
  have hmodpow : ∀ a : ℕ, ζ ^ a = ζ ^ (a % ℓ) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a ℓ, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hmod : m ^ ℓ ^ k % ℓ = m % ℓ := by
    have h := ZMod.pow_card_pow (p := ℓ) (n := k) (m : ZMod ℓ)
    rw [← Nat.cast_pow] at h
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  calc σ ζ = ζ ^ m := hm'
    _ = ζ ^ (m ^ ℓ ^ k) := by rw [hmodpow m, hmodpow (m ^ ℓ ^ k), hmod]
    _ = (σ ^ ℓ ^ k) ζ := (hpow _).symm
    _ = ζ := hfixk

variable (K Ksep) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Establish `hcard` using `natCard_rootsOfUnity_of_ne_zero K Ksep hℓK`. Establish `: Finite (rootsOfUnity ℓ Ksep)` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)`. Establish `: Nontrivial (rootsOfUnity ℓ Ksep)` using `Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)`. Take `⟨ζ, hζ⟩` from `exists_ne (1 : rootsOfUnity ℓ Ksep)`.

Establish `hζ0 : Additive.ofMul ζ ≠ 0` using `hζ`. Establish `hζp : ℓ • Additive.ofMul ζ = 0`. Establish `h` using `pow_card_eq_one' (G := rootsOfUnity ℓ Ksep) (x := ζ)`. Rewrite `h` using `[hcard]`. Rewrite using `[← ofMul_pow, h]`.

Both sides reduce to the same expression. Conclude with `⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩`.
-/
theorem nonempty_zmod_addEquiv_rootsOfUnity {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ Ksep)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard := natCard_rootsOfUnity_of_ne_zero K Ksep hℓK
  have : Finite (rootsOfUnity ℓ Ksep) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ Ksep) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity ℓ Ksep)
  have hζ0 : Additive.ofMul ζ ≠ 0 := hζ
  have hζp : ℓ • Additive.ofMul ζ = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ Ksep) (x := ζ)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

/- English proof (translation)
Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Take `⟨P, hP⟩` from `exists_isProSylow (G := Gal(Ksep/K)) (p := ℓ)`. Establish `: CompactSpace P` using `isCompact_iff_compactSpace.1 hP.1.isCompact`. Rewrite using `[← cdp_eq_of_isProSylow hℓ hP]`. Express the relevant statement in the definitionally equal form `cdp ℓ P ≤ ((2 : ℕ) : ℕ∞)`.

Rewrite using `[cdp_le_iff_of_isProPGroup hℓ hP.2.1 2]`. Establish `hμ : Subsingleton (cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3)`. It suffices to establish `h : ∀ x : cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩`. Introduce `x`. Take `⟨U, hU, hPU, y, rfl⟩` from `exists_cohomologyResLE_eq (galRootsOfUnity.{0} K Ksep ℓ) hP.1 3 x`.

Use `subsingleton_cohomology_three_rootsOfUnity K Ksep hℓK ⟨U, hU⟩` as an intermediate fact. Rewrite using `[Subsingleton.elim y 0, map_zero]`. Take `⟨e⟩` from `nonempty_zmod_addEquiv_rootsOfUnity K Ksep hℓ hℓK`. Establish `hfix : ∀ (σ : P) (x : Additive (rootsOfUnity ℓ Ksep)), (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x = x`. Introduce `σ x`.

Use `congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))` and prove the remaining obligations. Use `apply_eq_of_isProPGroup hℓ hP.2.1 σ.2 ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ _).1 (Additive.toMul x).2, Units.val_one]`. Set `ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶ Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)` to `Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom), fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩`. Set `ψ' : Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ) ⟶ Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ))` to `Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom), fun σ => LinearMap.ext fun x => by`.

Express the relevant statement in the definitionally equal form `ULift.up (e.symm ((Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x)) = ULift.up (e.symm x)`. Rewrite using `[hfix]⟩`. Establish `hcomp : ψ ≫ ψ' = 𝟙 _`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `e.symm (e x.down) = x.down`.

Conclude with `e.symm_apply_apply x.down`. Establish `hinj : Function.Injective (cohomologyMap ψ 3).hom` using `fun x y h => by`. Establish `h'` using `congrArg (cohomologyMap ψ' 3).hom h`. Rewrite `h'` using `[← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp, cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply]`. Then use the resulting hypothesis. Conclude with `hinj.subsingleton`.
-/
theorem cdp_galois_le_two {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    cdp ℓ Gal(Ksep/K) ≤ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := Gal(Ksep/K)) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cdp_eq_of_isProSylow hℓ hP]
  change cdp ℓ P ≤ ((2 : ℕ) : ℕ∞)
  rw [cdp_le_iff_of_isProPGroup hℓ hP.2.1 2]

  have hμ : Subsingleton (cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3) := by
    suffices h : ∀ x : cohomology (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)) 3, x = 0 from
      ⟨fun x y => (h x).trans (h y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ := exists_cohomologyResLE_eq (galRootsOfUnity.{0} K Ksep ℓ) hP.1 3 x
    have := subsingleton_cohomology_three_rootsOfUnity K Ksep hℓK ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]

  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ksep hℓ hℓK
  have hfix : ∀ (σ : P) (x : Additive (rootsOfUnity ℓ Ksep)),
      (Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine apply_eq_of_isProPGroup hℓ hP.2.1 σ.2 ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ _).1 (Additive.toMul x).2, Units.val_one]
  let ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶
      Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ) ⟶
      Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype (galRootsOfUnity.{0} K Ksep ℓ)).ρ σ x)) =
          ULift.up (e.symm x)
        rw [hfix]⟩
  have hcomp : ψ ≫ ψ' = 𝟙 _ := by
    ext x
    change e.symm (e x.down) = x.down
    exact e.symm_apply_apply x.down
  have hinj : Function.Injective (cohomologyMap ψ 3).hom := fun x y h => by
    have h' := congrArg (cohomologyMap ψ' 3).hom h
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp,
      cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply] at h'
  exact hinj.subsingleton

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `fun h0 => hn (by simp [h0])`. Establish `htors : IsAddTorsion M` using `fun m => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn0, hM m⟩`. It suffices to establish `h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩`. Introduce `x`. Use `eq_zero_of_primaryComponent_eq_bot n hn0 (fun ℓ hℓ hℓn => ?_) x (nsmul_cohomology_eq_zero M hM r x)` and prove the remaining obligations.

Establish `hℓK : (ℓ : K) ≠ 0` using `fun h0 => hn (by`. Take `⟨c, hc⟩` from `hℓn`. Rewrite using `[hc, Nat.cast_mul, h0, zero_mul])`. Use `primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) M htors ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem subsingleton_cohomology_of_three_le {n : ℕ} (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0)
    {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn0, hM m⟩
  suffices h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn0 (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  have hℓK : (ℓ : K) ≠ 0 := fun h0 => hn (by
    obtain ⟨c, hc⟩ := hℓn
    rw [hc, Nat.cast_mul, h0, zero_mul])
  refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) M htors ?_
  calc cdp ℓ (U : Subgroup Gal(Ksep/K)) ≤ cdp ℓ Gal(Ksep/K) := cdp_openSubgroup_le ℓ U
    _ ≤ 2 := cdp_galois_le_two K Ksep hℓ hℓK
    _ < r := by exact_mod_cast (show 2 < r by omega)

end Sylow

end GroundTheory.ProfCoh
