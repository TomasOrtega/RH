import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClass
import GroundTheory.GlobalFields.Adele.WeakApproxUnits

open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def coprimeIdeals : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' v _ := by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coprimeIdeals {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I ∈ 𝔪.coprimeIdeals ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
  Iff.rfl

/- English proof (translation)
Establish `h` using `((𝔪.mem_idelesOneMod.1 hx).1 v hv).1`. Rewrite `h` using `[coe_finiteProj]`. Rewrite using `[ord, h, log_one, neg_zero]`.
-/
theorem ord_eq_zero_of_mem_idelesOneMod {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.ideal) : ord v x = 0 := by
  have h := ((𝔪.mem_idelesOneMod.1 hx).1 v hv).1
  rw [coe_finiteProj] at h
  rw [ord, h, log_one, neg_zero]

/- English proof (translation)
The claim follows from `fun v hv ↦ by rw [count_toFractionalIdeal, 𝔪.ord_eq_zero_of_mem_idelesOneMod hx hv]`.
-/
theorem toFractionalIdeal_mem_coprimeIdeals {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    toFractionalIdeal x ∈ 𝔪.coprimeIdeals := fun v hv ↦ by
  rw [count_toFractionalIdeal, 𝔪.ord_eq_zero_of_mem_idelesOneMod hx hv]

/- English proof (translation)
Rewrite using `[← toFractionalIdeal_diagonal]`. Conclude with `𝔪.toFractionalIdeal_mem_coprimeIdeals ha`.
-/
theorem toPrincipalIdeal_mem_coprimeIdeals {a : Kˣ} (ha : a ∈ 𝔪.rayUnits) :
    toPrincipalIdeal (𝓞 K) K a ∈ 𝔪.coprimeIdeals := by
  rw [← toFractionalIdeal_diagonal]
  exact 𝔪.toFractionalIdeal_mem_coprimeIdeals ha

def principalRay : Subgroup 𝔪.coprimeIdeals :=
  (𝔪.rayUnits.map (toPrincipalIdeal (𝓞 K) K)).subgroupOf 𝔪.coprimeIdeals

/- English proof (translation)
Rewrite using `[principalRay, Subgroup.mem_subgroupOf, Subgroup.mem_map]`.
-/
theorem mem_principalRay {I : 𝔪.coprimeIdeals} :
    I ∈ 𝔪.principalRay ↔
      ∃ a ∈ 𝔪.rayUnits, toPrincipalIdeal (𝓞 K) K a = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  rw [principalRay, Subgroup.mem_subgroupOf, Subgroup.mem_map]

abbrev IdealRayClassGroup : Type _ :=
  𝔪.coprimeIdeals ⧸ 𝔪.principalRay

/- English proof (translation)
Set `S : Finset (HeightOneSpectrum (𝓞 K))` to `𝔪.finite_support_exponent.toFinset`. Set `T : Finset (InfinitePlace K)` to `Finset.univ`. Set `O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ))` to `(Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)}) ×ˢ (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal, (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real → 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((z * infiniteProj w.1 …`. Establish `hO : IsOpen O`. Use `(isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)` and prove the remaining obligations.

Conclude with `(isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)`. Simplify using `only [Set.ofPred_forall]`. Use `isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_` and prove the remaining obligations. Conclude with `isOpen_lt continuous_const ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp (Units.continuous_val.comp (continuous_mul_const _)))`. Establish `hne : O.Nonempty`.

Use `⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹), Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩` and prove the remaining obligations. Use `show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`. Introduce `hw _ show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)`.

Rewrite using `[inv_mul_cancel, Units.val_one, map_one]`. Conclude with `one_pos`. Take `⟨a, ha⟩` from `(denseRange_units_prod_pi S T).exists_mem_open hO hne`. Use `⟨a, 𝔪.mem_idelesOneMod.2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩` and prove the remaining obligations. Establish `hvS : v ∈ S`.

Rewrite using `[Set.Finite.mem_toFinset, mem_support, ← Nat.one_le_iff_ne_zero]`. Conclude with `(𝔪.one_le_exponent_iff v).2 hv`. Establish `h` using `Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩`. Establish `he : finiteProj v (diagonal K a) = Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a`. Use `Units.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a`. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion]`. Both sides reduce to the same expression. Rewrite using `[map_mul, he]`. Conclude with `h`.

Establish `h` using `Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw`. Establish `he : infiniteProj w.1 (diagonal K a) = Units.map (algebraMap K w.1.Completion).toMonoidHom a` using `Units.ext rfl`. Rewrite using `[map_mul, he]`. Conclude with `h`.
-/
theorem exists_diagonal_mul_mem_idelesOneMod (x : IdeleGroup K) :
    ∃ a : Kˣ, diagonal K a * x ∈ 𝔪.idelesOneMod := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := 𝔪.finite_support_exponent.toFinset
  let T : Finset (InfinitePlace K) := Finset.univ
  let O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ)) :=
    (Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)}) ×ˢ
      (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal,
        (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
            ((z * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)})
  have hO : IsOpen O := by
    refine (isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod
      (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)
    · exact (isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)
    · simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_
      exact isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
          (Units.continuous_val.comp (continuous_mul_const _)))
  have hne : O.Nonempty := by
    refine ⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹),
      Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩
    · show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)
      rw [inv_mul_cancel]
      exact one_mem _
    · intro hw _
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)
      rw [inv_mul_cancel, Units.val_one, map_one]
      exact one_pos
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S T).exists_mem_open hO hne
  refine ⟨a, 𝔪.mem_idelesOneMod.2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩
  · have hvS : v ∈ S := by
      rw [Set.Finite.mem_toFinset, mem_support, ← Nat.one_le_iff_ne_zero]
      exact (𝔪.one_le_exponent_iff v).2 hv
    have h := Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩
    have he : finiteProj v (diagonal K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
      refine Units.ext ?_
      change ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [map_mul, he]
    exact h
  · have h := Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw
    have he : infiniteProj w.1 (diagonal K a) =
        Units.map (algebraMap K w.1.Completion).toMonoidHom a :=
      Units.ext rfl
    rw [map_mul, he]
    exact h

def idelesOneModToCoprimeIdeals : 𝔪.idelesOneMod →* 𝔪.coprimeIdeals :=
  ((toFractionalIdeal (K := K)).comp 𝔪.idelesOneMod.subtype).codRestrict _
    fun x ↦ 𝔪.toFractionalIdeal_mem_coprimeIdeals x.2

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_idelesOneModToCoprimeIdeals (x : 𝔪.idelesOneMod) :
    ((𝔪.idelesOneModToCoprimeIdeals x : 𝔪.coprimeIdeals) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : IdeleGroup K) :=
  rfl

def toIdealRayClassGroup : 𝔪.idelesOneMod →* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneModToCoprimeIdeals

def toRayClassGroup : 𝔪.idelesOneMod →* 𝔪.RayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneMod.subtype

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer K`. Establish `hne : ((π : K) : v.adicCompletion K) ≠ 0`. Introduce `h`. Establish `h'` using `congrArg Valued.v h`. Rewrite `h'` using `[valuedAdicCompletion_eq_valuation', hπ, map_zero]`.

Conclude with `exp_ne_zero h'`. Use `⟨finiteEmbedding v (Units.mk0 _ hne), 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩, toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩` and prove the remaining obligations. Establish `hwv : w ≠ v` using `fun h ↦ hv (h ▸ hw)`. Rewrite using `[finiteProj_finiteEmbedding_of_ne hwv]`. Conclude with `one_mem _`.

Express the relevant statement in the definitionally equal form `0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)`. Rewrite using `[map_one]`. Conclude with `one_pos`. Rewrite using `[count_primeIdealUnit] split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp, neg_neg]`. Conclude with `ord_finiteEmbedding_of_ne h _`.
-/
theorem exists_mem_idelesOneMod_toFractionalIdeal_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ x ∈ 𝔪.idelesOneMod, toFractionalIdeal x = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
        neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

/- English proof (translation)
Introduce and unpack `⟨I, hI⟩`. Establish `h : I ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K` using `K)) := by`. Rewrite using `[← finprod_primeIdealUnit_zpow_count I]`. Use `finprod_induction (· ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K))) (one_mem _) (fun _ _ ↦ mul_mem) fun v ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hv : v.asIdeal ∣ 𝔪.ideal`.

Rewrite using `[hI v hv, zpow_zero]`. Conclude with `one_mem _`. Take `⟨x, hx, hxI⟩` from `𝔪.exists_mem_idelesOneMod_toFractionalIdeal_eq hv`. Conclude with `zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hxI⟩) _`. Take `⟨x, hx, hxI⟩` from `h`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext hxI⟩`.
-/
theorem idelesOneModToCoprimeIdeals_surjective : Surjective 𝔪.idelesOneModToCoprimeIdeals := by
  rintro ⟨I, hI⟩
  have h : I ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K)) := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    refine finprod_induction (· ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K))) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ ?_
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨x, hx, hxI⟩ := 𝔪.exists_mem_idelesOneMod_toFractionalIdeal_eq hv
      exact zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hxI⟩) _
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext hxI⟩

/- English proof (translation)
The claim follows from `(QuotientGroup.mk'_surjective _).comp 𝔪.idelesOneModToCoprimeIdeals_surjective`.
-/
theorem toIdealRayClassGroup_surjective : Surjective 𝔪.toIdealRayClassGroup :=
  (QuotientGroup.mk'_surjective _).comp 𝔪.idelesOneModToCoprimeIdeals_surjective

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Take `⟨a, ha⟩` from `𝔪.exists_diagonal_mul_mem_idelesOneMod x`. Use `⟨⟨_, ha⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (diagonal K a * x) : 𝔪.RayClassGroup) = QuotientGroup.mk x`.

Rewrite using `[QuotientGroup.eq, show (diagonal K a * x)⁻¹ * x = (diagonal K a)⁻¹ by`. Rewrite using `[mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel, mul_one]]`. Conclude with `inv_mem (𝔪.diagonal_range_le_rayGroup ⟨a, rfl⟩)`.
-/
theorem toRayClassGroup_surjective : Surjective 𝔪.toRayClassGroup := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha⟩ := 𝔪.exists_diagonal_mul_mem_idelesOneMod x
  refine ⟨⟨_, ha⟩, ?_⟩
  change (QuotientGroup.mk (diagonal K a * x) : 𝔪.RayClassGroup) = QuotientGroup.mk x
  rw [QuotientGroup.eq, show (diagonal K a * x)⁻¹ * x = (diagonal K a)⁻¹ by
    rw [mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel, mul_one]]
  exact inv_mem (𝔪.diagonal_range_le_rayGroup ⟨a, rfl⟩)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, toRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]`. Both sides reduce to the same expression.
-/
theorem ker_toRayClassGroup :
    𝔪.toRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext x
  rw [MonoidHom.mem_ker, toRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

/- English proof (translation)
Use extensionality with `⟨x, hx⟩`. Rewrite using `[MonoidHom.mem_ker, toIdealRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_principalRay, Subgroup.mem_subgroupOf, rayGroup, Subgroup.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hax⟩`. Express the relevant statement in the definitionally equal form `toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal x at hax`.

Use `⟨diagonal K a, ⟨a, rfl⟩, (diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩` and prove the remaining obligations. Rewrite using `[congruenceSubgroup_eq_inf, Subgroup.mem_inf, ← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, toFractionalIdeal_diagonal, hax]`. Conclude with `⟨mul_mem (inv_mem ha) hx, inv_mul_cancel _⟩`. Introduce and unpack `⟨_, ⟨a, rfl⟩, u, hu, rfl⟩`. Establish `hu'` using `𝔪.congruenceSubgroup_le_idelesOneMod hu`.

Establish `ha : a ∈ 𝔪.rayUnits`. Express the relevant statement in the definitionally equal form `diagonal K a ∈ 𝔪.idelesOneMod`. Rewrite using `[← mul_inv_cancel_right (diagonal K a) u]`. Conclude with `mul_mem hx (inv_mem hu')`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal (diagonal K a * u)`. Establish `hu0 : toFractionalIdeal u = 1`. Rewrite using `[← MonoidHom.mem_ker, ker_toFractionalIdeal]`. Conclude with `𝔪.congruenceSubgroup_le_standardOpenSubgroup hu`. Rewrite using `[map_mul, hu0, mul_one, toFractionalIdeal_diagonal]`.
-/
theorem ker_toIdealRayClassGroup :
    𝔪.toIdealRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext ⟨x, hx⟩
  rw [MonoidHom.mem_ker, toIdealRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_principalRay, Subgroup.mem_subgroupOf, rayGroup, Subgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, hax⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal x at hax
    refine ⟨diagonal K a, ⟨a, rfl⟩, (diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    rw [congruenceSubgroup_eq_inf, Subgroup.mem_inf, ← ker_toFractionalIdeal, MonoidHom.mem_ker,
      map_mul, map_inv, toFractionalIdeal_diagonal, hax]
    exact ⟨mul_mem (inv_mem ha) hx, inv_mul_cancel _⟩
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
    have hu' := 𝔪.congruenceSubgroup_le_idelesOneMod hu
    have ha : a ∈ 𝔪.rayUnits := by
      change diagonal K a ∈ 𝔪.idelesOneMod
      rw [← mul_inv_cancel_right (diagonal K a) u]
      exact mul_mem hx (inv_mem hu')
    refine ⟨a, ha, ?_⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal (diagonal K a * u)
    have hu0 : toFractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker, ker_toFractionalIdeal]
      exact 𝔪.congruenceSubgroup_le_standardOpenSubgroup hu
    rw [map_mul, hu0, mul_one, toFractionalIdeal_diagonal]

def rayClassGroupEquiv : 𝔪.RayClassGroup ≃* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (𝔪.ker_toRayClassGroup.trans 𝔪.ker_toIdealRayClassGroup.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toIdealRayClassGroup_surjective))

/- English proof (translation)
Establish `h : (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm (QuotientGroup.mk x : 𝔪.RayClassGroup) = QuotientGroup.mk ⟨x, hx⟩`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[rayClassGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h]`. Both sides reduce to the same expression.
-/
theorem rayClassGroupEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassGroupEquiv (QuotientGroup.mk x : 𝔪.RayClassGroup) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm
      (QuotientGroup.mk x : 𝔪.RayClassGroup) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [rayClassGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

def quotientEquivIdealRayClassGroup :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.IdealRayClassGroup :=
  𝔪.quotientMapCongruenceEquiv.trans 𝔪.rayClassGroupEquiv

/- English proof (translation)
Rewrite using `[quotientEquivIdealRayClassGroup, MulEquiv.trans_apply, quotientMapCongruenceEquiv_mk, rayClassGroupEquiv_mk _ hx]`.
-/
theorem quotientEquivIdealRayClassGroup_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.quotientEquivIdealRayClassGroup (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  rw [quotientEquivIdealRayClassGroup, MulEquiv.trans_apply, quotientMapCongruenceEquiv_mk,
    rayClassGroupEquiv_mk _ hx]

def idealRayClassGroupEquiv_of_real_eq_univ (h : 𝔪.real = Set.univ) :
    _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal ≃* 𝔪.IdealRayClassGroup :=
  (𝔪.rayClassGroupEquiv_of_real_eq_univ h).symm.trans 𝔪.rayClassGroupEquiv

instance : Finite 𝔪.IdealRayClassGroup :=
  Finite.of_equiv _ 𝔪.rayClassGroupEquiv.toEquiv

end Modulus

end

end GroundTheory.Global
