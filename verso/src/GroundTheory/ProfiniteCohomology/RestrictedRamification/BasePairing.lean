import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ZmodToQZGsCompactInvLocalToCompactEqLocalInvU
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [Fintype S] [NeZero n] in
/- English proof (translation)
Establish `h` using `zmodCocycleHom_mul z 1 1`. Rewrite `h` using `[mul_one]`. Conclude with `(add_eq_left.1 h.symm)`.
-/
theorem zmodCocycleHom_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    zmodCocycleHom z 1 = 0 := by
  have h := zmodCocycleHom_mul z 1 1
  rw [mul_one] at h
  exact (add_eq_left.1 h.symm)

omit [Fintype S] in

def gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)) where
  toFun g := Multiplicative.ofAdd (zmodCocycleHom z g)
  map_one' := by rw [zmodCocycleHom_one]; rfl
  map_mul' g h := by rw [zmodCocycleHom_mul]; rfl
  continuous_toFun := ((isLocallyConstant_zmodCocycleHom z).comp Multiplicative.ofAdd).continuous

omit [Fintype S] [NeZero n] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toAdd_gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (g : galUnramifiedOutside K.1 ℚ̄ S) : Multiplicative.toAdd (gsCharOfCocycle S n z g) = zmodCocycleHom z g :=
  rfl

omit [Fintype S] [NeZero n] in

/- English proof (translation)
Apply `cocycles_ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Establish `hv : v = ![v 0]` using `by funext i; fin_cases i; rfl`. Establish `e : zmodCocycleHom z (v 0) = 0` using `congrArg Multiplicative.toAdd (DFunLike.congr_fun hz (v 0))`. Rewrite using `[hv]`.

Apply `ULift.ext` to reduce the goal to its premises. Conclude with `e.trans (congrArg (fun w => (cochainOf (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) w ![v 0]).down) (map_zero (cocycleι (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))).symm`.
-/
theorem eq_zero_of_gsCharOfCocycle_eq_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hz : gsCharOfCocycle S n z = 1) : z = 0 := by
  apply cocycles_ext
  funext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  have e : zmodCocycleHom z (v 0) = 0 := congrArg Multiplicative.toAdd (DFunLike.congr_fun hz (v 0))
  rw [hv]
  apply ULift.ext
  exact e.trans (congrArg (fun w => (cochainOf (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) w ![v 0]).down)
    (map_zero (cocycleι (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))).symm

omit [Fintype S] [NeZero n] in

/- English proof (translation)
Establish `hf : IsLocallyConstant fun g => (ULift.up (Multiplicative.toAdd (χ g)) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)` using `((IsLocallyConstant.iff_continuous (fun g : galUnramifiedOutside K.1 ℚ̄ S => χ g)).2 χ.continuous).comp fun x : Multiplicative (ZMod n) => (ULift.up (Multiplicative.toAdd x) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)`. Establish `hmul : ∀ g h : galUnramifiedOutside K.1 ℚ̄ S, (ULift.up (Multiplicative.toAdd (χ (g * h))) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) = ULift.up (Multiplicative.toAdd (χ g)) + ULift.up (Multiplicative.toAdd (χ h))` using `fun g h => by`. Apply `ULift.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Multiplicative.toAdd (χ (g * h)) = Multiplicative.toAdd (χ g) + Multiplicative.toAdd (χ h)`. Rewrite using `[map_mul, toAdd_mul]`.

Use `⟨cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (fun _ _ => rfl) _ hf hmul, ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Rewrite using `[toAdd_gsCharOfCocycle]`. Conclude with `congrArg ULift.down (cochainOf_cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (fun _ _ => rfl) _ hf hmul ![g])`.
-/
theorem exists_gsCharOfCocycle_eq
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) :
    ∃ z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (gsCharOfCocycle S n z : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) = χ := by
  have hf : IsLocallyConstant fun g => (ULift.up (Multiplicative.toAdd (χ g)) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) :=
    ((IsLocallyConstant.iff_continuous (fun g : galUnramifiedOutside K.1 ℚ̄ S => χ g)).2 χ.continuous).comp
      fun x : Multiplicative (ZMod n) => (ULift.up (Multiplicative.toAdd x) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
  have hmul : ∀ g h : galUnramifiedOutside K.1 ℚ̄ S,
      (ULift.up (Multiplicative.toAdd (χ (g * h))) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) =
        ULift.up (Multiplicative.toAdd (χ g)) + ULift.up (Multiplicative.toAdd (χ h)) := fun g h => by
    apply ULift.ext
    change Multiplicative.toAdd (χ (g * h)) = Multiplicative.toAdd (χ g) + Multiplicative.toAdd (χ h)
    rw [map_mul, toAdd_mul]
  refine ⟨cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (fun _ _ => rfl) _ hf hmul, ?_⟩
  ext g
  apply Multiplicative.toAdd.injective
  rw [toAdd_gsCharOfCocycle]
  exact congrArg ULift.down (cochainOf_cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (fun _ _ => rfl) _ hf hmul ![g])

variable (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

omit [Fintype S] [NeZero n] in
include hnk hS in
/- English proof (translation)
Introduce `v hv` and use `by subst hnk exact pow_notMem_asIdeal_of_forall S ℓ k hS v hv`.
-/
theorem hnS_of_hS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv => by
  subst hnk
  exact pow_notMem_asIdeal_of_forall S ℓ k hS v hv

include hℓ hnk hS in

/- English proof (translation)
The claim follows from `zmodToQZ_injective (n := n) (zmodToQZ_gsCompactInv_gsCupClass S ιs n hnS ℓ k hℓ hnk hS hodd h3 d z (gsCharOfCocycle S n z) (fun _ => rfl))`.
-/
theorem gsCompactInv_gsCupClass (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (d : GsUnitsDatum S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) =
      Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z)
        (Additive.toMul (gsUnitsClass S d))) :=
  zmodToQZ_injective (n := n) (zmodToQZ_gsCompactInv_gsCupClass S ιs n hnS ℓ k hℓ hnk hS hodd h3 d z
    (gsCharOfCocycle S n z) (fun _ => rfl))

omit [Fintype S] [NeZero n] in

/- English proof (translation)
Establish `hmn : m.Coprime n` using `hnk ▸ hm.pow_right k`. Rewrite `h` using `[nsmul_eq_mul]`. Conclude with `(ZMod.unitOfCoprime m hmn).isUnit.mul_right_eq_zero.1 h`.
-/
theorem eq_zero_of_coprime_nsmul_zmod (hnk : n = ℓ ^ k) {m : ℕ} (hm : m.Coprime ℓ) {u : ZMod n}
    (h : m • u = 0) : u = 0 := by
  have hmn : m.Coprime n := hnk ▸ hm.pow_right k
  rw [nsmul_eq_mul] at h
  exact (ZMod.unitOfCoprime m hmn).isUnit.mul_right_eq_zero.1 h

set_option maxHeartbeats 1600000 in
include hℓ hnk hS in

/- English proof (translation)
Establish `hnS` using `hnS_of_hS S n ℓ k hnk hS`. Establish `hz` using `cohomologyπ_surjective (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 x`. Assume the negation of the conclusion as `hne`. Establish `hχ : gsCharOfCocycle S n hz.choose ≠ 1` using `fun h => hne (hz.choose_spec.symm.trans ((congrArg (cohomologyπ _ 1) (eq_zero_of_gsCharOfCocycle_eq_one S n _ h)).trans (map_zero _)))`. Establish `hψ : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) ≠ 1` using `fun h => hχ ((MulEquiv.map_eq_one_iff _).1 h)`.

Establish `ha : ∃ a, charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) a ≠ 1` using `not_forall.1 fun h => hψ (MonoidHom.ext h)`. Establish `hm` using `exists_coprime_gsUnitsClass_eq S ℓ hℓ hS (Additive.ofMul ha.choose)`. Establish `hd` using `hm.choose_spec.2`. Establish `h1 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS hd.choose hz.choose) = 0` using `(congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs hd.choose))) w …`. Establish `h2` using `(gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS hd.choose hz.choose).symm.trans h1`.

Establish `h4 : Additive.toMul (gsUnitsClass S hd.choose) = ha.choose ^ hm.choose` using `(congrArg Additive.toMul hd.choose_spec).trans (toMul_nsmul _ _)`. Establish `h5 : hm.choose • Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) ha.choose) = 0` using `(toAdd_pow _ _).symm.trans ((congrArg Multiplicative.toAdd (map_pow _ _ _)).symm.trans ((congrArg (fun u => Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) u)) h4).symm.trans h2))`. Conclude with `ha.choose_spec (Multiplicative.toAdd.injective (eq_zero_of_coprime_nsmul_zmod n ℓ k hnk hm.choose_spec.1 h5))`.
-/
theorem gsCompactInv_ker_left (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hx : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    x = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  have hz := cohomologyπ_surjective (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 x
  by_contra hne
  have hχ : gsCharOfCocycle S n hz.choose ≠ 1 := fun h => hne (hz.choose_spec.symm.trans
    ((congrArg (cohomologyπ _ 1) (eq_zero_of_gsCharOfCocycle_eq_one S n _ h)).trans (map_zero _)))
  have hψ : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) ≠ 1 :=
    fun h => hχ ((MulEquiv.map_eq_one_iff _).1 h)
  have ha : ∃ a, charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) a ≠ 1 :=
    not_forall.1 fun h => hψ (MonoidHom.ext h)
  have hm := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS (Additive.ofMul ha.choose)
  have hd := hm.choose_spec.2
  have h1 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS hd.choose hz.choose) = 0 :=
    (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
      ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
        (gsUnitsData S ιs hd.choose))) w)) hz.choose_spec).trans (hx _)
  have h2 := (gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS hd.choose hz.choose).symm.trans h1
  have h4 : Additive.toMul (gsUnitsClass S hd.choose) = ha.choose ^ hm.choose :=
    (congrArg Additive.toMul hd.choose_spec).trans (toMul_nsmul _ _)
  have h5 : hm.choose • Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose)
      ha.choose) = 0 :=
    (toAdd_pow _ _).symm.trans ((congrArg Multiplicative.toAdd (map_pow _ _ _)).symm.trans
      ((congrArg (fun u => Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) u))
        h4).symm.trans h2))
  exact ha.choose_spec (Multiplicative.toAdd.injective
    (eq_zero_of_coprime_nsmul_zmod n ℓ k hnk hm.choose_spec.1 h5))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `set N := (nsmulAddMonoidHom (α := A) n).range`. Establish `hq : (QuotientAddGroup.mk' N a) ≠ 0` using `fun h0 => hne ((QuotientAddGroup.eq_zero_iff a).1 h0 |>.elim fun b hb => ⟨b, hb⟩)`. Establish `htors : ∀ q : A ⧸ N, n • q = 0` using `fun q => QuotientAddGroup.induction_on q fun x => by`. Rewrite using `[← QuotientAddGroup.mk_nsmul]`.

Conclude with `(QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩`. Take `⟨f, hf⟩` from `zmod_exists_apply_ne_zero htors hq`. Conclude with `hf (h (f.comp (QuotientAddGroup.mk' N)))`.
-/
theorem exists_nsmul_eq_of_forall_zmod {A : Type*} [AddCommGroup A] (a : A)
    (h : ∀ f : A →+ ZMod n, f a = 0) : ∃ b, n • b = a := by
  by_contra hne
  set N := (nsmulAddMonoidHom (α := A) n).range
  have hq : (QuotientAddGroup.mk' N a) ≠ 0 := fun h0 =>
    hne ((QuotientAddGroup.eq_zero_iff a).1 h0 |>.elim fun b hb => ⟨b, hb⟩)
  have htors : ∀ q : A ⧸ N, n • q = 0 := fun q =>
    QuotientAddGroup.induction_on q fun x => by
      rw [← QuotientAddGroup.mk_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩
  obtain ⟨f, hf⟩ := zmod_exists_apply_ne_zero htors hq
  exact hf (h (f.comp (QuotientAddGroup.mk' N)))

set_option maxHeartbeats 4000000 in
include hℓ hnk hS in

/- English proof (translation)
Establish `hnS` using `hnS_of_hS S n ℓ k hnk hS`. Distinguish the cases in `hk : k = 0`. Establish `hn1 : n = 1` using `by rw [hnk, hk, pow_zero]`. Establish `e` using `nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) 2 y`. Substitute `hn1` using the available equality.

Conclude with `(one_smul _ _).symm.trans e`. Establish `hoddℓ : Odd ℓ ∨ IsTotallyComplex K.1` using `hodd.imp (fun h => Nat.not_even_iff_odd.1 fun he => Nat.not_even_iff_odd.2 (hnk ▸ h) (Nat.even_pow.2 ⟨he, hk⟩)) id`. Take `⟨h, hh⟩` from `surjective_gsKummerCompactδ S ιs n hnS ℓ k hℓ hnk hS hoddℓ ((gsRootsComparison S ιs n 2).hom y)`. Take `⟨d, hd⟩` from `gsUnitsData_surjective S ιs h`. Establish `hyeq : y = (gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d))` using `(hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans (congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom (hh.symm.trans (congrArg (gsKummerCompactδ S ιs n hnS 1).hom hd.symm)))`.

Establish `hall : ∀ f : Additive (SIdeleClassGroup S) →+ ZMod n, f (gsUnitsClass S d) = 0`. Introduce `f`. Take `⟨z, hz⟩` from `exists_gsCharOfCocycle_eq S n ((charEquiv ℚ̄ (Set.toFinite S) hodd).symm (AddMonoidHom.toMultiplicative f))`. Establish `e1` using `gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS d z`. Establish `e2 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) = 0` using `(congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) w (cohomologyπ _ 1 z))) hyeq).symm.trans (hy _)`.

Establish `e3 : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z) = AddMonoidHom.toMultiplicative f` using `(congrArg (charEquiv ℚ̄ (Set.toFinite S) hodd) hz).trans (MulEquiv.apply_symm_apply _ _)`. Conclude with `(congrArg (fun ψ => Multiplicative.toAdd (ψ (Additive.toMul (gsUnitsClass S d)))) e3).symm.trans (e1.symm.trans e2)`. Take `⟨b, hb⟩` from `exists_nsmul_eq_of_forall_zmod n (A := Additive (SIdeleClassGroup S)) _ hall`. Take `⟨m, hm, d', hd'⟩` from `exists_coprime_gsUnitsClass_eq S ℓ hℓ hS b`. Establish `hc0 : gsUnitsClass S (m • d - n • d') = 0`.

Rewrite using `[map_sub, map_nsmul, map_nsmul, ← hb, hd']`. Conclude with `sub_eq_zero_of_eq ((smul_smul m n b).trans ((congrArg (· • b) (mul_comm m n)).trans (smul_smul n m b).symm))`. Establish `hd0` using `gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero S ιs _ hc0`. Rewrite `hd0` using `[map_sub, map_nsmul, map_nsmul, sub_eq_zero, hd]`. Establish `hw1 : m • (gsRootsComparison S ιs n 2).hom y = 0`.

Rewrite using `[← hh, ← map_nsmul, hd0, map_nsmul, nsmul_gsRootsCompact S ιs n hnS]`. Establish `hw2 : ℓ ^ k • (gsRootsComparison S ιs n 2).hom y = 0`. Rewrite using `[← hnk]`. Conclude with `nsmul_gsRootsCompact S ιs n hnS 2 _`. Establish `hw` using `eq_zero_of_coprime_nsmul_eq_zero hm hw1 hw2`.

Conclude with `(hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans ((congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom hw).trans (map_zero _))`.
-/
theorem gsCompactInv_ker_right (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (hy : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    y = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  by_cases hk : k = 0
  · have hn1 : n = 1 := by rw [hnk, hk, pow_zero]
    have e := nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) 2 y
    subst hn1
    exact (one_smul _ _).symm.trans e
  have hoddℓ : Odd ℓ ∨ IsTotallyComplex K.1 :=
    hodd.imp (fun h => Nat.not_even_iff_odd.1 fun he => Nat.not_even_iff_odd.2 (hnk ▸ h) (Nat.even_pow.2 ⟨he, hk⟩)) id
  obtain ⟨h, hh⟩ := surjective_gsKummerCompactδ S ιs n hnS ℓ k hℓ hnk hS hoddℓ ((gsRootsComparison S ιs n 2).hom y)
  obtain ⟨d, hd⟩ := gsUnitsData_surjective S ιs h
  have hyeq : y = (gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
      (gsUnitsData S ιs d)) :=
    (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
      (congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom
        (hh.symm.trans (congrArg (gsKummerCompactδ S ιs n hnS 1).hom hd.symm)))

  have hall : ∀ f : Additive (SIdeleClassGroup S) →+ ZMod n, f (gsUnitsClass S d) = 0 := by
    intro f
    obtain ⟨z, hz⟩ := exists_gsCharOfCocycle_eq S n
      ((charEquiv ℚ̄ (Set.toFinite S) hodd).symm (AddMonoidHom.toMultiplicative f))
    have e1 := gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS d z
    have e2 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) = 0 :=
      (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) w
        (cohomologyπ _ 1 z))) hyeq).symm.trans (hy _)
    have e3 : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z) = AddMonoidHom.toMultiplicative f :=
      (congrArg (charEquiv ℚ̄ (Set.toFinite S) hodd) hz).trans (MulEquiv.apply_symm_apply _ _)
    exact (congrArg (fun ψ => Multiplicative.toAdd (ψ (Additive.toMul (gsUnitsClass S d)))) e3).symm.trans
      (e1.symm.trans e2)
  obtain ⟨b, hb⟩ := exists_nsmul_eq_of_forall_zmod n (A := Additive (SIdeleClassGroup S)) _ hall
  obtain ⟨m, hm, d', hd'⟩ := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS b
  have hc0 : gsUnitsClass S (m • d - n • d') = 0 := by
    rw [map_sub, map_nsmul, map_nsmul, ← hb, hd']
    exact sub_eq_zero_of_eq ((smul_smul m n b).trans ((congrArg (· • b) (mul_comm m n)).trans (smul_smul n m b).symm))
  have hd0 := gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero S ιs _ hc0
  rw [map_sub, map_nsmul, map_nsmul, sub_eq_zero, hd] at hd0
  have hw1 : m • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hh, ← map_nsmul, hd0, map_nsmul, nsmul_gsRootsCompact S ιs n hnS]
  have hw2 : ℓ ^ k • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hnk]
    exact nsmul_gsRootsCompact S ιs n hnS 2 _
  have hw := eq_zero_of_coprime_nsmul_eq_zero hm hw1 hw2
  exact (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
    ((congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom hw).trans (map_zero _))

end

end GroundTheory.ProfCoh
