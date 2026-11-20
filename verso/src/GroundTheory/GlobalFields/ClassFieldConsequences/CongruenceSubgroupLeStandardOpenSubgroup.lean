import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

structure Modulus where

  ideal : Ideal (𝓞 K)
  ideal_ne_bot : ideal ≠ ⊥

  real : Set {w : InfinitePlace K // w.IsReal}

variable {K}

namespace IdeleGroup

def positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)}
  one_mem' w _ := by simp
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (ha w hw)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_positiveAt {S : Set {w : InfinitePlace K // w.IsReal}} {x : IdeleGroup K} :
    x ∈ positiveAt S ↔ ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) :=
  Iff.rfl

/- English proof (translation)
Establish `: (positiveAt S : Set (IdeleGroup K)) = ⋂ w ∈ S, (fun x : IdeleGroup K ↦ InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)) ⁻¹' Set.Ioi 0`. Use extensionality with `x`. Simplify using `[mem_positiveAt]`. Rewrite using `[this]`. Use `S.toFinite.isOpen_biInter fun w _ ↦ isOpen_Ioi.preimage ?_` and prove the remaining obligations.

Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp (Units.continuous_val.comp (continuous_infiniteProj w.1))`.
-/
theorem isOpen_positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) :
    IsOpen (positiveAt S : Set (IdeleGroup K)) := by
  have : (positiveAt S : Set (IdeleGroup K)) = ⋂ w ∈ S, (fun x : IdeleGroup K ↦
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)) ⁻¹' Set.Ioi 0 := by
    ext x
    simp [mem_positiveAt]
  rw [this]
  refine S.toFinite.isOpen_biInter fun w _ ↦ isOpen_Ioi.preimage ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    (Units.continuous_val.comp (continuous_infiniteProj w.1))

end IdeleGroup

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def exponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  multiplicity v.asIdeal 𝔪.ideal

omit [NumberField K] in
/- English proof (translation)
The claim follows from `multiplicity_eq_zero`.
-/
theorem exponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) :
    𝔪.exponent v = 0 ↔ ¬ v.asIdeal ∣ 𝔪.ideal :=
  multiplicity_eq_zero

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[Nat.one_le_iff_ne_zero, Ne, exponent_eq_zero_iff, not_not]`.
-/
theorem one_le_exponent_iff (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ 𝔪.exponent v ↔ v.asIdeal ∣ 𝔪.ideal := by
  rw [Nat.one_le_iff_ne_zero, Ne, exponent_eq_zero_iff, not_not]

omit [NumberField K] in

/- English proof (translation)
The claim follows from `pow_multiplicity_dvd _ _`.
-/
theorem asIdeal_pow_exponent_dvd (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ 𝔪.exponent v ∣ 𝔪.ideal :=
  pow_multiplicity_dvd _ _

/- English proof (translation)
Establish `hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal ^ multiplicity v.asIdeal 𝔪.ideal`. Simplify `Ideal.hasFiniteMulSupport 𝔪.ideal_ne_bot` using `only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity 𝔪.ideal_ne_bot]`. Rewrite using `[← mulSupport_asIdeal_pow]`. Conclude with `hm`.
-/
theorem finite_support_exponent : (support 𝔪.exponent).Finite := by
  have hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ multiplicity v.asIdeal 𝔪.ideal := by
    simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity 𝔪.ideal_ne_bot] using
      Ideal.hasFiniteMulSupport 𝔪.ideal_ne_bot
  rw [← mulSupport_asIdeal_pow]
  exact hm

def congruenceSubgroup : Subgroup (IdeleGroup K) :=
  (idealLevel 𝔪.ideal).comap (toFinite K) ⊓ positiveAt 𝔪.real

/- English proof (translation)
Rewrite using `[congruenceSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, idealLevel, mem_finiteLevel, mem_positiveAt]`. Simplify using `only [finiteComponent_toFinite]`. Both sides reduce to the same expression.
-/
theorem mem_congruenceSubgroup {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, finiteProj v x ∈ unitsLevel v (𝔪.exponent v)) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  rw [congruenceSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, idealLevel, mem_finiteLevel,
    mem_positiveAt]
  simp only [finiteComponent_toFinite]
  rfl

/- English proof (translation)
Rewrite using `[mem_congruenceSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hf, hi⟩`. Use `⟨fun v hv ↦ (hf v).2, fun v hv ↦ (hf v).1, hi⟩` and prove the remaining obligations. Introduce and unpack `⟨hd, hn, hi⟩`.

Use `⟨fun v ↦ ?_, hi⟩` and prove the remaining obligations. Distinguish the cases in `hv : v.asIdeal ∣ 𝔪.ideal`. Conclude with `(mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv)).2 (hd v hv)`. Rewrite using `[(𝔪.exponent_eq_zero_iff v).2 hv, mem_unitsLevel]`. Use `⟨hn v hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.cast_zero, neg_zero, exp_zero]`. Conclude with `Valuation.map_sub_le _ (hn v hv).le (by simp)`.
-/
theorem mem_congruenceSubgroup_iff {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal →
          Valued.v ((x : 𝔸[K]).2 v - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        (∀ v, ¬ v.asIdeal ∣ 𝔪.ideal → Valued.v ((x : 𝔸[K]).2 v) = 1) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((x : 𝔸[K]).1 w.1) := by
  rw [mem_congruenceSubgroup]
  constructor
  · rintro ⟨hf, hi⟩
    refine ⟨fun v hv ↦ (hf v).2, fun v hv ↦ (hf v).1, hi⟩
  · rintro ⟨hd, hn, hi⟩
    refine ⟨fun v ↦ ?_, hi⟩
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · exact (mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv)).2 (hd v hv)
    · rw [(𝔪.exponent_eq_zero_iff v).2 hv, mem_unitsLevel]
      refine ⟨hn v hv, ?_⟩
      rw [Nat.cast_zero, neg_zero, exp_zero]
      exact Valuation.map_sub_le _ (hn v hv).le (by simp)

/- English proof (translation)
Rewrite using `[congruenceSubgroup, Subgroup.coe_inf, Subgroup.coe_comap]`. Use `IsOpen.inter ?_ (isOpen_positiveAt _)` and prove the remaining obligations. Conclude with `(isOpen_finiteLevel 𝔪.finite_support_exponent).preimage (continuous_toFinite K)`.
-/
theorem isOpen_congruenceSubgroup : IsOpen (𝔪.congruenceSubgroup : Set (IdeleGroup K)) := by
  rw [congruenceSubgroup, Subgroup.coe_inf, Subgroup.coe_comap]
  refine IsOpen.inter ?_ (isOpen_positiveAt _)
  exact (isOpen_finiteLevel 𝔪.finite_support_exponent).preimage (continuous_toFinite K)

/- English proof (translation)
The claim follows from `fun x hx ↦ by rw [mem_standardOpenSubgroup_iff_toFinite_mem] exact finiteLevel_le_finiteLevel_zero _ (Subgroup.mem_inf.1 hx).1`.
-/
theorem congruenceSubgroup_le_standardOpenSubgroup :
    𝔪.congruenceSubgroup ≤ standardOpenSubgroup K := fun x hx ↦ by
  rw [mem_standardOpenSubgroup_iff_toFinite_mem]
  exact finiteLevel_le_finiteLevel_zero _ (Subgroup.mem_inf.1 hx).1

def idelesOneMod : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v.asIdeal ∣ 𝔪.ideal),
    (unitsLevel v (𝔪.exponent v)).comap (finiteProj v)) ⊓ positiveAt 𝔪.real

/- English proof (translation)
Simplify using `only [idelesOneMod, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_positiveAt]`.
-/
theorem mem_idelesOneMod {x : IdeleGroup K} :
    x ∈ 𝔪.idelesOneMod ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal → finiteProj v x ∈ unitsLevel v (𝔪.exponent v)) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  simp only [idelesOneMod, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_positiveAt]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Subgroup.mem_inf, mem_congruenceSubgroup, mem_idelesOneMod, mem_standardOpenSubgroup_iff_toFinite_mem, mem_finiteLevel]`. Simplify using `only [finiteComponent_toFinite, Pi.zero_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hf, hi⟩`.

Conclude with `⟨⟨fun v _ ↦ hf v, hi⟩, fun v ↦ unitsLevel_antitone v (Nat.zero_le _) (hf v)⟩`. Introduce and unpack `⟨⟨hf, hi⟩, h0⟩`. Use `⟨fun v ↦ ?_, hi⟩` and prove the remaining obligations. Distinguish the cases in `hv : v.asIdeal ∣ 𝔪.ideal`. Conclude with `hf v hv`.

Rewrite using `[(𝔪.exponent_eq_zero_iff v).2 hv]`. Conclude with `h0 v`.
-/
theorem congruenceSubgroup_eq_inf :
    𝔪.congruenceSubgroup = 𝔪.idelesOneMod ⊓ standardOpenSubgroup K := by
  ext x
  rw [Subgroup.mem_inf, mem_congruenceSubgroup, mem_idelesOneMod,
    mem_standardOpenSubgroup_iff_toFinite_mem, mem_finiteLevel]
  simp only [finiteComponent_toFinite, Pi.zero_apply]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨⟨fun v _ ↦ hf v, hi⟩, fun v ↦ unitsLevel_antitone v (Nat.zero_le _) (hf v)⟩
  · rintro ⟨⟨hf, hi⟩, h0⟩
    refine ⟨fun v ↦ ?_, hi⟩
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · exact hf v hv
    · rw [(𝔪.exponent_eq_zero_iff v).2 hv]
      exact h0 v

/- English proof (translation)
Rewrite using `[congruenceSubgroup_eq_inf]`. Conclude with `inf_le_left`.
-/
theorem congruenceSubgroup_le_idelesOneMod : 𝔪.congruenceSubgroup ≤ 𝔪.idelesOneMod := by
  rw [congruenceSubgroup_eq_inf]
  exact inf_le_left

def rayUnits : Subgroup Kˣ :=
  𝔪.idelesOneMod.comap (diagonal K)

/- English proof (translation)
Rewrite using `[rayUnits, Subgroup.mem_comap, mem_idelesOneMod]`. Use `and_congr (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_) (forall_congr' fun w ↦ forall_congr' fun _ ↦ ?_)` and prove the remaining obligations. Establish `hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k` using `fun k ↦ by`. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion]`. Both sides reduce to the same expression.

Rewrite using `[mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv), coe_finiteProj_diagonal, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hc, hc, (algebraMap K (v.adicCompletion K)).map_sub, (algebraMap K (v.adicCompletion K)).map_one]`. Rewrite using `[coe_infiniteProj_diagonal]`. Conclude with `Iff.of_eq (congrArg (0 < ·) (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe _ _))`.
-/
theorem mem_rayUnits {a : Kˣ} :
    a ∈ 𝔪.rayUnits ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal → v.valuation K ((a : K) - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K) := by
  rw [rayUnits, Subgroup.mem_comap, mem_idelesOneMod]
  refine and_congr (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_)
    (forall_congr' fun w ↦ forall_congr' fun _ ↦ ?_)
  · have hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k := fun k ↦ by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv), coe_finiteProj_diagonal,
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hc, hc,
      (algebraMap K (v.adicCompletion K)).map_sub, (algebraMap K (v.adicCompletion K)).map_one]
  · rw [coe_infiniteProj_diagonal]
    exact Iff.of_eq (congrArg (0 < ·) (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe _ _))

end Modulus

end

end GroundTheory.Global
