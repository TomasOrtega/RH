import Mathlib
import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
import GroundTheory.ProfiniteCohomology.LocalTateDuality.NormCharacters
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField

attribute [local instance 2000] Rep.hV2

attribute [local irreducible] localClassFormationOfIsSepClosure

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a * b)) = Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) + Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) b)`. Rewrite using `[map_mul, ofMul_mul]`.
-/
theorem unitsInvariantOpen_mul (W : Subgroup Gal(Ksep/K)) (a b : (fixedField W)ˣ) :
    unitsInvariantOpen W (a * b) = unitsInvariantOpen W a + unitsInvariantOpen W b := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a * b)) =
    Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) +
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) b)
  rw [map_mul, ofMul_mul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap K (fixedField W))]`. Conclude with `(map_ne_zero_iff _ (algebraMap K (fixedField W)).injective).2 hn`.
-/
theorem natCast_fixedField_ne_zero (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (n : fixedField W) ≠ 0 := by
  rw [← map_natCast (algebraMap K (fixedField W))]
  exact (map_ne_zero_iff _ (algebraMap K (fixedField W)).injective).2 hn

/- English proof (translation)
Set `` to `GroundTheory.LocalField.algebraicValuativeRel K Ksep`. Set `` to `GroundTheory.LocalField.algebraicTopology K Ksep`. Use `GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep` as an intermediate fact. Use `GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep` as an intermediate fact. Establish `hfinE : Finite ((fixedField (U : Subgroup Gal(Ksep/K)))ˣ ⧸ (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range)` using `GroundTheory.LocalField.finite_quotient_range_pow (natCast_fixedField_ne_zero hn _)`.

Set `κ : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* Multiplicative (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)` to `{ toFun := fun a => Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a))) map_one' := by`. Establish `h` using `unitsInvariantOpen_pow (U : Subgroup Gal(Ksep/K)) 1 0`. Rewrite `h` using `[pow_zero, zero_smul]`. Rewrite using `[h, map_zero, map_zero, ofAdd_zero]`. Use the proof step `map_mul' := fun a b => by`.

Rewrite using `[unitsInvariantOpen_mul, map_add, map_add, ofAdd_add] }`. Establish `hle : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range ≤ κ.ker`. Introduce and unpack `_ ⟨b, rfl⟩`. Rewrite using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) (b ^ n)))) = 1`.

Rewrite using `[δ_unitsInvariantOpen_pow_eq_zero hn, ofAdd_zero]`. Use `Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ κ hle q)) fun y => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `exists_δ_unitsInvariantOpen_eq hn U y`. Conclude with `⟨(a : _ ⧸ (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range), rfl⟩`.
-/
theorem finite_cohomology_one_res_galRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Finite (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1) := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  have hfinE : Finite ((fixedField (U : Subgroup Gal(Ksep/K)))ˣ ⧸
      (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range) :=
    GroundTheory.LocalField.finite_quotient_range_pow (natCast_fixedField_ne_zero hn _)
  let κ : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      Multiplicative (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep n)) 1) :=
    { toFun := fun a => Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K)))
        0 1 rfl).hom ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)))
      map_one' := by
        have h := unitsInvariantOpen_pow (U : Subgroup Gal(Ksep/K)) 1 0
        rw [pow_zero, zero_smul] at h
        rw [h, map_zero, map_zero, ofAdd_zero]
      map_mul' := fun a b => by
        rw [unitsInvariantOpen_mul, map_add, map_add, ofAdd_add] }
  have hle : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range ≤ κ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom
      ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) (b ^ n)))) = 1
    rw [δ_unitsInvariantOpen_pow_eq_zero hn, ofAdd_zero]
  refine Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ κ hle q)) fun y => ?_
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  exact ⟨(a : _ ⧸ (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range), rfl⟩

/- English proof (translation)
Set `` to `GroundTheory.LocalField.algebraicValuativeRel K Ksep`. Set `` to `GroundTheory.LocalField.algebraicTopology K Ksep`. Use `GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep` as an intermediate fact. Use `GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep` as an intermediate fact. Take `⟨z, rfl⟩` from `cohomologyπ_surjective _ 1 x`.

Establish `hnorm` using `fun a => (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)`. Establish `hopen : IsOpen (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))))`. Establish `e : (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) = (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0}`. Use extensionality with `g`. Conclude with `mem_charKer`.

Rewrite using `[e]`. Conclude with `(isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)`. Establish `hcomm : ∀ σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))), σ * τ * σ⁻¹ * τ⁻¹ ∈ charKer (charAdd (openChar n U z))` using `fun σ τ => by`. Rewrite using `[mem_charKer, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add, map_add, map_neg, map_neg]`. Normalize the expressions using the abelian group laws.

Establish `htop` using `eq_top_of_forall_exists_norm _ hopen hcomm hnorm`. Rewrite using `[cohomologyπ_one_eq_zero_iff_of_trivial _ (fun _ _ => rfl)]`. Conclude with `fun g => ULift.ext _ _ (zmodCocycleHom_eq_zero_of_charKer_eq_top hn U z htop g)`.
-/
theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : ∀ y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    x = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  have hnorm := fun a => (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)
  have hopen : IsOpen (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) := by
    have e : (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) =
        (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    rw [e]
    exact (isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)
  have hcomm : ∀ σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))),
      σ * τ * σ⁻¹ * τ⁻¹ ∈ charKer (charAdd (openChar n U z)) := fun σ τ => by
    rw [mem_charKer, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add, map_add,
      map_neg, map_neg]
    abel
  have htop := eq_top_of_forall_exists_norm _ hopen hcomm hnorm
  rw [cohomologyπ_one_eq_zero_iff_of_trivial _ (fun _ _ => rfl)]
  exact fun g => ULift.ext _ _ (zmodCocycleHom_eq_zero_of_charKer_eq_top hn U z htop g)

/- English proof (translation)
Set `` to `GroundTheory.LocalField.algebraicValuativeRel K Ksep`. Set `` to `GroundTheory.LocalField.algebraicTopology K Ksep`. Use `GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep` as an intermediate fact. Use `GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep` as an intermediate fact. Take `⟨a, rfl⟩` from `exists_δ_unitsInvariantOpen_eq hn U y`.

Distinguish the cases in `ha : ∃ b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ, b ^ n = a`. Take `⟨b, rfl⟩` from `ha`. Conclude with `δ_unitsInvariantOpen_pow_eq_zero hn _ b`. Simplify using `only [not_exists] at ha`. Take `⟨ψ, hψo, hψ⟩` from `exists_zmod_char_not_norm (Ω := Ksep) (natCast_fixedField_ne_zero hn _) a ha`.

Take `⟨z, hz⟩` from `exists_cocycle_charKer_eq hn U ψ hψo`. Conclude with `(hψ (exists_norm_of_eq (congrArg fixedField hz) ((cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)))).elim`.
-/
theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K))
    (y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
    (h : ∀ x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    y = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  by_cases ha : ∃ b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ, b ^ n = a
  · obtain ⟨b, rfl⟩ := ha
    exact δ_unitsInvariantOpen_pow_eq_zero hn _ b
  · simp only [not_exists] at ha
    obtain ⟨ψ, hψo, hψ⟩ := exists_zmod_char_not_norm (Ω := Ksep) (natCast_fixedField_ne_zero hn _) a ha
    obtain ⟨z, hz⟩ := exists_cocycle_charKer_eq hn U ψ hψo
    exact (hψ (exists_norm_of_eq (congrArg fixedField hz)
      ((cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)))).elim

/- English proof (translation)
Establish `: NeZero n` using `⟨ne_zero_of_natCast_ne_zero' hn⟩`. Use `set β := bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn))) (show 1 + 1 = 2 from rfl)) with hβ`. Use `set t := (localInvRootsOfUnity hn U).toAddMonoidHom with ht`. Establish `ht0 : ∀ c, t c = 0 → c = 0` using `fun c hc => (localInvRootsOfUnity hn U).injective (hc.trans (map_zero _).symm)`. Establish `h1 : Function.Injective ((AddMonoidHom.compHom t).comp β)`.

Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Use `eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x fun y => ht0 _ ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun hx y`. Establish `h2 : Function.Injective ((AddMonoidHom.compHom t).comp β.flip)`. Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations.

Use `eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right hn U y fun x => ht0 _ ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun hy x`. Establish `hYfin` using `finite_cohomology_one_res_galRootsOfUnity hn U`. Establish `hXfin : Finite (cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)` using `Finite.of_injective _ h1`. Establish `c1` using `Nat.card_le_card_of_injective _ h1`.

Establish `c2` using `Nat.card_le_card_of_injective _ h2`. Establish `c3` using `card_addMonoidHom_zmod_le (n := n) (A := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)`. Establish `c4` using `card_addMonoidHom_zmod_le (n := n) (A := cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)`. Conclude with `⟨h1.bijective_of_nat_card_le (by omega), h2.bijective_of_nat_card_le (by omega)⟩`.
-/
theorem isPerfectPairing_localInvRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
        (show 1 + 1 = 2 from rfl)))
      (localInvRootsOfUnity hn U).toAddMonoidHom := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  set β := bilinAddHom (cupPairing (zmodMulPairing n
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
    (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
    (show 1 + 1 = 2 from rfl)) with hβ
  set t := (localInvRootsOfUnity hn U).toAddMonoidHom with ht
  have ht0 : ∀ c, t c = 0 → c = 0 := fun c hc =>
    (localInvRootsOfUnity hn U).injective (hc.trans (map_zero _).symm)
  have h1 : Function.Injective ((AddMonoidHom.compHom t).comp β) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x fun y => ht0 _ ?_
    exact DFunLike.congr_fun hx y
  have h2 : Function.Injective ((AddMonoidHom.compHom t).comp β.flip) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right hn U y fun x => ht0 _ ?_
    exact DFunLike.congr_fun hy x
  have hYfin := finite_cohomology_one_res_galRootsOfUnity hn U
  have hXfin : Finite (cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1) :=
    Finite.of_injective _ h1
  have c1 := Nat.card_le_card_of_injective _ h1
  have c2 := Nat.card_le_card_of_injective _ h2
  have c3 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
  have c4 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
  exact ⟨h1.bijective_of_nat_card_le (by omega), h2.bijective_of_nat_card_le (by omega)⟩

end GroundTheory.ProfCoh
