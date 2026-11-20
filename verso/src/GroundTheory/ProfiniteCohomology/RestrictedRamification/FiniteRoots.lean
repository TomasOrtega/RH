import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicFinite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.GlobalFields.SUnits
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section General

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)

include hnS in

/- English proof (translation)
Use `(AddMonoidHom.finite_iff_finite_ker_range (kummerPicHom (Ω := Ω) S n)).2 ⟨?_, inferInstance⟩` and prove the remaining obligations. Set `k` to `kummerSUnitsHom (Ω := Ω) S n hnS`. Establish `: Module.Finite ℤ (Additive (S.unit F))` using `inferInstance`. Establish `: AddGroup.FG (Additive (S.unit F))` using `Module.Finite.iff_addGroup_fg.1 this`. Establish `: AddGroup.FG k.range` using `AddGroup.fg_of_surjective k.rangeRestrict_surjective`.

Establish `htor : IsAddTorsion k.range`. Introduce and unpack `⟨_, a, rfl⟩`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `n • k a = 0`.

Rewrite using `[← map_nsmul]`. Conclude with `(kummerSUnitsHom_eq_zero_iff (Ω := Ω) S n hnS _).2 ⟨a, rfl⟩`. Establish `: Finite k.range` using `AddCommGroup.finite_of_fg_isAddTorsion _ htor`. Use `Finite.of_injective (β := k.range) (fun y => ⟨y.1, ?_⟩) ?_` and prove the remaining obligations. Conclude with `(kummerPicHom_eq_zero_iff (Ω := Ω) S n hnS y.1).1 y.2`.

Introduce `y z h`. Simplify using `only at h`. Conclude with `Subtype.ext (Subtype.mk.inj h)`.
-/
theorem finite_cohomology_one_rootsOfUnity [Finite S] :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1) := by
  refine (AddMonoidHom.finite_iff_finite_ker_range (kummerPicHom (Ω := Ω) S n)).2 ⟨?_, inferInstance⟩
  let k := kummerSUnitsHom (Ω := Ω) S n hnS
  have : Module.Finite ℤ (Additive (S.unit F)) := inferInstance
  have : AddGroup.FG (Additive (S.unit F)) := Module.Finite.iff_addGroup_fg.1 this
  have : AddGroup.FG k.range := AddGroup.fg_of_surjective k.rangeRestrict_surjective
  have htor : IsAddTorsion k.range := by
    rintro ⟨_, a, rfl⟩
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), ?_⟩
    apply Subtype.ext
    change n • k a = 0
    rw [← map_nsmul]
    exact (kummerSUnitsHom_eq_zero_iff (Ω := Ω) S n hnS _).2 ⟨a, rfl⟩
  have : Finite k.range := AddCommGroup.finite_of_fg_isAddTorsion _ htor
  refine Finite.of_injective (β := k.range) (fun y => ⟨y.1, ?_⟩) ?_
  · exact (kummerPicHom_eq_zero_iff (Ω := Ω) S n hnS y.1).1 y.2
  · intro y z h
    simp only at h
    exact Subtype.ext (Subtype.mk.inj h)

include hnS in

/- English proof (translation)
Establish `hK` using `sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS`. Set `f` to `(cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 2).hom.toAddMonoidHom`. Use `(AddMonoidHom.finite_iff_finite_ker_range f).2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Finite (cohomology (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ 1)` using `Finite.of_injective _ (h1SUnitsToSPic_injective (Ω := Ω) S)`. Set `d` to `(δ hK 1 2 rfl).hom.toAddMonoidHom`.

Establish `: Finite d.range` using `Set.finite_coe_iff.2 (Set.finite_range d)`. Use `Finite.of_injective (β := d.range) (fun y => ⟨y.1, ?_⟩) ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 1 2 rfl) y.1 y.2`. Conclude with `⟨z, hz⟩`. Introduce `y z h`.

Simplify using `only at h`. Conclude with `Subtype.ext (Subtype.mk.inj h)`. Use `show Finite (SetLike.coe f.range)`. Use `(hfin.subset ?_).to_subtype` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `h1` using `cohomologyMap_g_cohomologyMap_f_apply (S := sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n) 2 x`. Establish `hg : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).g 2).hom (f x) = n • f x` using `cohomologyMap_nsmul_id_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n 2 (f x)`. Conclude with `hg.symm.trans h1`.
-/
theorem finite_cohomology_two_rootsOfUnity_of_finite
    (hfin : {y : cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 2 | n • y = 0}.Finite) :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 2) := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  let f := (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 2).hom.toAddMonoidHom
  refine (AddMonoidHom.finite_iff_finite_ker_range f).2 ⟨?_, ?_⟩
  · have : Finite (cohomology (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ 1) :=
      Finite.of_injective _ (h1SUnitsToSPic_injective (Ω := Ω) S)
    let d := (δ hK 1 2 rfl).hom.toAddMonoidHom
    have : Finite d.range := Set.finite_coe_iff.2 (Set.finite_range d)
    refine Finite.of_injective (β := d.range) (fun y => ⟨y.1, ?_⟩) ?_
    · obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 1 2 rfl) y.1 y.2
      exact ⟨z, hz⟩
    · intro y z h
      simp only at h
      exact Subtype.ext (Subtype.mk.inj h)
  · show Finite (SetLike.coe f.range)
    refine (hfin.subset ?_).to_subtype
    rintro _ ⟨x, rfl⟩
    have h1 := cohomologyMap_g_cohomologyMap_f_apply
      (S := sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n) 2 x
    have hg : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).g 2).hom (f x) =
        n • f x :=
      cohomologyMap_nsmul_id_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n 2 (f x)
    exact hg.symm.trans h1

end General

section Brauer

open GroundTheory.Global FiniteSubfield DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

/- English proof (translation)
Take `⟨c, hc⟩` from `hd`. Use `hS v ?_` and prove the remaining obligations. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hv`.
-/
theorem mem_of_dvd_of_mem {d n : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  obtain ⟨c, hc⟩ := hd
  refine hS v ?_
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hv

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on generalizing y with`. Consider the case `_ n ih`. Distinguish the cases in `h1 : n = 1`. Substitute `h1` using the available equality. Simplify using `using hy`.

Establish `hℓ : n.minFac.Prime` using `Nat.minFac_prime h1`. Take `⟨a, m, hm, hn⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hℓ.ne_one`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn0 (hn.trans (mul_zero _))`.

Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hn` using `[pow_zero, one_mul]`. Conclude with `hm (hn ▸ Nat.minFac_dvd n)`. Establish `hmy : m • y = 0`.

Use `eq_zero_of_sUnitsBrauer_eq_zero K S _ hℓ (mem_of_dvd_of_mem K S (Nat.minFac_dvd _) hS) (m • y) a ?_ ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hn, hy]`. Rewrite using `[map_nsmul, hy', nsmul_zero]`. Establish `hlt : m < n`. Establish `h2 : 1 < n.minFac ^ a` using `Nat.one_lt_pow ha hℓ.one_lt`.

Rewrite using `[hn]`. Conclude with `lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) h2`. Conclude with `ih m hlt hm0 (mem_of_dvd_of_mem K S ⟨n.minFac ^ a, hn.trans (mul_comm _ _)⟩ hS) y hmy hy'`.
-/
theorem eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : n • y = 0) (hy' : sUnitsBrauer K S y = 0) :
    y = 0 := by
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    simpa using hy
  have hℓ : n.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hℓ.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn0 (hn.trans (mul_zero _))
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn
    exact hm (hn ▸ Nat.minFac_dvd n)
  have hmy : m • y = 0 := by
    refine eq_zero_of_sUnitsBrauer_eq_zero K S _ hℓ
      (mem_of_dvd_of_mem K S (Nat.minFac_dvd _) hS) (m • y) a ?_ ?_
    · rw [smul_smul, ← hn, hy]
    · rw [map_nsmul, hy', nsmul_zero]
  have hlt : m < n := by
    have h2 : 1 < n.minFac ^ a := Nat.one_lt_pow ha hℓ.one_lt
    rw [hn]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) h2
  exact ih m hlt hm0 (mem_of_dvd_of_mem K S ⟨n.minFac ^ a, hn.trans (mul_comm _ _)⟩ hS) y hmy hy'

/- English proof (translation)
Take `⟨ιs⟩` from `nonempty_localEmbeddings K`. Set `T : Set QZ` to `{u | n • u = 0}`. Establish `: Finite T` using `(AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hn0)).to_subtype`. Set `t` to `(brauerLocal ιs).comp (sUnitsBrauer K S)`. Establish `ht : ∀ y : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}, ∀ v : Place K.1, placeInv v (t y.1 v) ∈ T`.

Introduce `y v`. Express the relevant statement in the definitionally equal form `n • placeInv v (t y.1 v) = 0`. Establish `e : (n • t y.1) v = n • (t y.1 v)` using `map_nsmul (DFinsupp.evalAddMonoidHom v) n (t y.1)`. Rewrite using `[← map_nsmul, ← e, ← map_nsmul t, y.2, map_zero, DFinsupp.zero_apply, map_zero]`. Set `Φ : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0} → (InfinitePlace K.1 → T) × (S → T)` to `fun y => (fun w => ⟨placeInv (.inl w) (t y.1 (.inl w)), ht y _⟩, fun w => ⟨placeInv (.inr w.1) (t y.1 (.inr w.1)), ht y _⟩)`.

Use `Set.finite_coe_iff.1 (Finite.of_injective Φ fun y z h => ?_)` and prove the remaining obligations. Establish `htyz : t y.1 = t z.1`. Use extensionality with `v`. Break down `v with w | w` into its components or cases. Conclude with `placeInv_injective (.inl w) (congrArg Subtype.val (congrFun (congrArg Prod.fst h) w))`.

Distinguish the cases in `hw : w ∈ S`. Conclude with `placeInv_injective (.inr w) (congrArg Subtype.val (congrFun (congrArg Prod.snd h) ⟨w, hw⟩))`. Conclude with `(brauerLocal_sUnitsBrauer_inr K S ιs y.1 w hw).trans (brauerLocal_sUnitsBrauer_inr K S ιs z.1 w hw).symm`. Establish `hyz : sUnitsBrauer K S (y.1 - z.1) = 0`. Use `brauerLocal_injective ιs ?_` and prove the remaining obligations.

Rewrite using `[map_sub, map_sub, map_zero]`. Conclude with `sub_eq_zero.2 htyz`. Establish `h0` using `eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero K S n hn0 hS (y.1 - z.1) (by rw [smul_sub, y.2, z.2, sub_zero]) hyz`. Conclude with `Subtype.ext (sub_eq_zero.1 h0)`.
-/
theorem finite_nsmul_eq_zero_sUnits_two [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}.Finite := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let T : Set QZ := {u | n • u = 0}
  have : Finite T := (AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hn0)).to_subtype
  let t := (brauerLocal ιs).comp (sUnitsBrauer K S)
  have ht : ∀ y : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}, ∀ v : Place K.1,
      placeInv v (t y.1 v) ∈ T := by
    intro y v
    change n • placeInv v (t y.1 v) = 0
    have e : (n • t y.1) v = n • (t y.1 v) := map_nsmul (DFinsupp.evalAddMonoidHom v) n (t y.1)
    rw [← map_nsmul, ← e, ← map_nsmul t, y.2, map_zero, DFinsupp.zero_apply, map_zero]
  let Φ : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0} →
      (InfinitePlace K.1 → T) × (S → T) := fun y =>
    (fun w => ⟨placeInv (.inl w) (t y.1 (.inl w)), ht y _⟩,
      fun w => ⟨placeInv (.inr w.1) (t y.1 (.inr w.1)), ht y _⟩)
  refine Set.finite_coe_iff.1 (Finite.of_injective Φ fun y z h => ?_)
  have htyz : t y.1 = t z.1 := by
    ext v
    rcases v with w | w
    · exact placeInv_injective (.inl w) (congrArg Subtype.val (congrFun (congrArg Prod.fst h) w))
    · by_cases hw : w ∈ S
      · exact placeInv_injective (.inr w)
          (congrArg Subtype.val (congrFun (congrArg Prod.snd h) ⟨w, hw⟩))
      · exact (brauerLocal_sUnitsBrauer_inr K S ιs y.1 w hw).trans
          (brauerLocal_sUnitsBrauer_inr K S ιs z.1 w hw).symm
  have hyz : sUnitsBrauer K S (y.1 - z.1) = 0 := by
    refine brauerLocal_injective ιs ?_
    rw [map_sub, map_sub, map_zero]
    exact sub_eq_zero.2 htyz
  have h0 := eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero K S n hn0 hS (y.1 - z.1)
    (by rw [smul_sub, y.2, z.2, sub_zero]) hyz
  exact Subtype.ext (sub_eq_zero.1 h0)

/- English proof (translation)
Establish `: NeZero n` using `⟨hn0⟩`. Establish `hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal` using `fun v hv h => hv (hS v h)`. Use `interval_cases r`. Establish `: Finite (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n)` using `inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))`. Conclude with `finite_cohomology_zero _`.

Conclude with `finite_cohomology_one_rootsOfUnity S n hnS`. Conclude with `finite_cohomology_two_rootsOfUnity_of_finite S n hnS (finite_nsmul_eq_zero_sUnits_two K S n hn0 hS)`.
-/
theorem finite_cohomology_rootsOfUnity [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (r : ℕ)
    (hr : r ≤ 2) :
    Finite (cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) r) := by
  have : NeZero n := ⟨hn0⟩
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  interval_cases r
  · have : Finite (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
    exact finite_cohomology_zero _
  · exact finite_cohomology_one_rootsOfUnity S n hnS
  · exact finite_cohomology_two_rootsOfUnity_of_finite S n hnS
      (finite_nsmul_eq_zero_sUnits_two K S n hn0 hS)

end Brauer

end GroundTheory.ProfCoh
