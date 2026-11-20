import Mathlib
import GroundTheory.LocalFields.LowerIndex

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Filter Topology MeasureTheory

def enatMin (n : ℕ∞) (a : ℝ) : ℝ :=
  ENat.recTopCoe a (fun m ↦ min (m : ℝ) a) n

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem enatMin_top (a : ℝ) : enatMin ⊤ a = a :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem enatMin_coe (m : ℕ) (a : ℝ) : enatMin m a = min (m : ℝ) a :=
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem enatMin_nonneg (n : ℕ∞) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ enatMin n a := by
  induction n using ENat.recTopCoe with
  | top => simpa using ha
  | coe m => simp [ha]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem enatMin_mono (n : ℕ∞) : Monotone (enatMin n) := by
  induction n using ENat.recTopCoe with
  | top => exact monotone_id
  | coe m => exact fun a b h ↦ by simpa using min_le_min_left _ h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem continuous_enatMin (n : ℕ∞) : Continuous (enatMin n) := by
  induction n using ENat.recTopCoe with
  | top => exact continuous_id
  | coe m => exact continuous_const.min continuous_id

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem enatMin_eq_self_iff {n : ℕ∞} {a : ℝ} : enatMin n a = a ↔ ∀ m : ℕ, n = m → a ≤ m := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m => simp

section

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def lowerRamificationGroupReal (t : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  lowerRamificationGroup K L ⌈t⌉

variable {K L}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mem_lowerRamificationGroupReal_iff {t : ℝ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroupReal K L t ↔ enatMin (lowerIndex K L σ) (t + 1) = t + 1 := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_lowerIndex, enatMin_eq_self_iff]
  generalize lowerIndex K L σ = n
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m =>
    simp only [Nat.cast_le, Nat.cast_inj, forall_eq']
    rw [Int.toNat_le, ← le_sub_iff_add_le, Int.ceil_le]
    push_cast
    constructor <;> intro h <;> linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq {t : ℝ} {σ : L ≃ₐ[K] L} {m : ℕ}
    (h : lowerIndex K L σ = m) : σ ∈ lowerRamificationGroupReal K L t ↔ t + 1 ≤ m := by
  rw [mem_lowerRamificationGroupReal_iff, h, enatMin_coe, min_eq_right_iff]

@[simp]
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lowerRamificationGroupReal_natCast (n : ℕ) :
    lowerRamificationGroupReal K L n = lowerRamificationGroup K L n := by
  rw [lowerRamificationGroupReal, Int.ceil_natCast]

@[simp]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lowerRamificationGroupReal_intCast (n : ℤ) :
    lowerRamificationGroupReal K L n = lowerRamificationGroup K L n := by
  rw [lowerRamificationGroupReal, Int.ceil_intCast]

variable (K L) in

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem lowerRamificationGroupReal_antitone : Antitone (lowerRamificationGroupReal K L) :=
  fun _ _ h ↦ lowerRamificationGroup_antitone K L (Int.ceil_mono h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowerRamificationGroupReal_eq_top {t : ℝ} (ht : t ≤ -1) :
    lowerRamificationGroupReal K L t = ⊤ :=
  lowerRamificationGroup_eq_top K L (Int.ceil_le.mpr (by push_cast; exact ht))

variable (K L) in

def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    ((lowerRamificationGroupReal K L t).relIndex (lowerRamificationGroup K L 0) : ℝ)⁻¹

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem relIndex_mul_card_inf {G : Type*} [Group G] (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card K := by
  rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index (H.subgroupOf K)]
  congr 1
  rw [← Subgroup.inf_subgroupOf_right]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

open Classical in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem inv_relIndex_eq_sum (t : ℝ) :
    ((lowerRamificationGroupReal K L t).relIndex (lowerRamificationGroup K L 0) : ℝ)⁻¹ =
      (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
        ∑ σ : L ≃ₐ[K] L, if σ ∈ lowerRamificationGroup K L 0 ∧
          σ ∈ lowerRamificationGroupReal K L t then (1 : ℝ) else 0 := by
  have hmul := relIndex_mul_card_inf (lowerRamificationGroupReal K L t)
    (lowerRamificationGroup K L 0)
  have hcount : (∑ σ : L ≃ₐ[K] L, if σ ∈ lowerRamificationGroup K L 0 ∧
      σ ∈ lowerRamificationGroupReal K L t then (1 : ℝ) else 0) =
        Nat.card ↥(lowerRamificationGroupReal K L t ⊓ lowerRamificationGroup K L 0) := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    ext σ
    simp [Subgroup.mem_inf, and_comm]
  rw [hcount]
  have hc : (Nat.card ↥(lowerRamificationGroupReal K L t ⊓ lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hmulR : ((lowerRamificationGroupReal K L t).relIndex (lowerRamificationGroup K L 0) : ℝ) *
      Nat.card ↥(lowerRamificationGroupReal K L t ⊓ lowerRamificationGroup K L 0) =
        Nat.card (lowerRamificationGroup K L 0) := by
    exact_mod_cast hmul
  rw [← hmulR, mul_inv, mul_assoc, inv_mul_cancel₀ hc, mul_one]

open Classical in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem antitone_indicator_lowerRamificationGroupReal (σ : L ≃ₐ[K] L) :
    Antitone fun t : ℝ ↦ if σ ∈ lowerRamificationGroup K L 0 ∧
      σ ∈ lowerRamificationGroupReal K L t then (1 : ℝ) else 0 := by
  intro a b hab
  by_cases hb : σ ∈ lowerRamificationGroup K L 0 ∧ σ ∈ lowerRamificationGroupReal K L b
  · have ha : σ ∈ lowerRamificationGroup K L 0 ∧ σ ∈ lowerRamificationGroupReal K L a :=
      ⟨hb.1, lowerRamificationGroupReal_antitone K L hab hb.2⟩
    simp only [ha, hb, and_self, if_true, le_refl]
  · simp only [hb, if_false]
    split_ifs <;> norm_num

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem integral_indicator_Iic {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ∫ t in (0 : ℝ)..u, (Set.Iic c).indicator (fun _ ↦ (1 : ℝ)) t = min u c := by
  rcases le_total 0 u with hu | hu
  · rw [intervalIntegral.integral_of_le hu, setIntegral_indicator measurableSet_Iic,
      Set.Ioc_inter_Iic]
    simp [hu, hc]
  · rw [intervalIntegral.integral_of_ge hu, setIntegral_indicator measurableSet_Iic,
      Set.Ioc_inter_Iic, min_eq_left hc, min_eq_left (hu.trans hc)]
    simp [hu]

open Classical in

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Proceed by induction.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem integral_indicator_lowerRamificationGroupReal (σ : L ≃ₐ[K] L) (u : ℝ) :
    ∫ t in (0 : ℝ)..u, (if σ ∈ lowerRamificationGroup K L 0 ∧
      σ ∈ lowerRamificationGroupReal K L t then (1 : ℝ) else 0) =
      if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) u else 0 := by
  by_cases h0 : σ ∈ lowerRamificationGroup K L 0
  · simp only [h0, true_and, if_true]
    have h1 := one_le_lowerIndex_iff.mpr h0
    generalize hn : lowerIndex K L σ = n at h1
    induction n using ENat.recTopCoe with
    | top =>
      have hall : ∀ t : ℝ, σ ∈ lowerRamificationGroupReal K L t := fun t ↦ by
        rw [mem_lowerRamificationGroupReal_iff, hn, enatMin_top]
      simp [hall]
    | coe m =>
      have hm : 1 ≤ m := by exact_mod_cast h1
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have heq : (fun t : ℝ ↦ if σ ∈ lowerRamificationGroupReal K L t then (1 : ℝ) else 0) =
          (Set.Iic ((m : ℝ) - 1)).indicator (fun _ ↦ 1) := by
        funext t
        simp only [Set.indicator, Set.mem_Iic, mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hn]
        congr 1
        apply propext
        constructor <;> intro h <;> linarith
      rw [heq, integral_indicator_Iic (by linarith), ← ENat.natCast_one, ← ENat.natCast_sub, enatMin_coe,
        Nat.cast_sub hm, Nat.cast_one, min_comm]
  · simp [h0]

open Classical in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem herbrandPhi_eq_sum (u : ℝ) :
    herbrandPhi K L u = (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, if σ ∈ lowerRamificationGroup K L 0 then
        enatMin (lowerIndex K L σ - 1) u else 0 := by
  rw [herbrandPhi]
  simp_rw [inv_relIndex_eq_sum]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp_rw [integral_indicator_lowerRamificationGroupReal]
  · intro σ _
    exact (antitone_indicator_lowerRamificationGroupReal σ).intervalIntegrable

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
open Classical in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem card_filter_mem {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    ((Finset.univ.filter (· ∈ H)).card : ℝ) = Nat.card H := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem card_lowerRamificationGroup_zero_pos :
    (0 : ℝ) < Nat.card (lowerRamificationGroup K L 0) := by
  exact_mod_cast Nat.card_pos

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Both sides reduce to the same expression. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem herbrandPhi_of_nonpos {u : ℝ} (hu : u ≤ 0) : herbrandPhi K L u = u := by
  classical
  rw [herbrandPhi_eq_sum]
  have h : ∀ σ : L ≃ₐ[K] L, (if σ ∈ lowerRamificationGroup K L 0 then
      enatMin (lowerIndex K L σ - 1) u else 0) =
        if σ ∈ lowerRamificationGroup K L 0 then u else 0 := by
    intro σ
    split_ifs
    · rw [enatMin_eq_self_iff]
      exact fun m _ ↦ hu.trans (Nat.cast_nonneg m)
    · rfl
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    card_filter_mem, ← mul_assoc, inv_mul_cancel₀ card_lowerRamificationGroup_zero_pos.ne', one_mul]

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPhi_zero : herbrandPhi K L 0 = 0 :=
  herbrandPhi_of_nonpos le_rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem herbrandPhi_eq_sum_lowerIndex {u : ℝ} (hu : -1 ≤ u) :
    herbrandPhi K L u = (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) - 1 := by
  classical
  have h : ∀ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) =
      (if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) u else 0) +
        if σ ∈ lowerRamificationGroup K L 0 then 1 else 0 := by
    intro σ
    by_cases h0 : σ ∈ lowerRamificationGroup K L 0
    · simp only [h0, if_true]
      have h1 := one_le_lowerIndex_iff.mpr h0
      generalize lowerIndex K L σ = n at h1
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have hm : 1 ≤ m := by exact_mod_cast h1
        rw [← ENat.natCast_one, ← ENat.natCast_sub, enatMin_coe, enatMin_coe, Nat.cast_sub hm,
          Nat.cast_one, ← min_add_add_right, sub_add_cancel]
    · simp only [h0, if_false, add_zero, lowerIndex_eq_zero_iff.mpr h0]
      rw [show ((0 : ℕ∞)) = ((0 : ℕ) : ℕ∞) from rfl, enatMin_coe, Nat.cast_zero]
      exact min_eq_left (by linarith)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_boole, card_filter_mem, herbrandPhi_eq_sum, mul_add,
    inv_mul_cancel₀ card_lowerRamificationGroup_zero_pos.ne', add_sub_cancel_right]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem herbrandPhi_strictMono : StrictMono (herbrandPhi K L) := by
  classical
  intro a b hab
  rw [herbrandPhi_eq_sum, herbrandPhi_eq_sum]
  refine mul_lt_mul_of_pos_left ?_ (inv_pos.mpr card_lowerRamificationGroup_zero_pos)
  refine Finset.sum_lt_sum (fun σ _ ↦ ?_) ⟨1, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact enatMin_mono _ hab.le
    · exact le_rfl
  · simp [(lowerRamificationGroup K L 0).one_mem, hab]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_herbrandPhi : Continuous (herbrandPhi K L) := by
  classical
  have h : herbrandPhi K L = fun u ↦ (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, if σ ∈ lowerRamificationGroup K L 0 then
        enatMin (lowerIndex K L σ - 1) u else 0 :=
    funext herbrandPhi_eq_sum
  rw [h]
  refine continuous_const.mul (continuous_finsetSum _ fun σ _ ↦ ?_)
  split_ifs
  · exact continuous_enatMin _
  · exact continuous_const

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tendsto_herbrandPhi_atTop : Tendsto (herbrandPhi K L) atTop atTop := by
  classical
  have hge : ∀ u ≥ (0 : ℝ), (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ * u ≤
      herbrandPhi K L u := by
    intro u hu
    rw [herbrandPhi_eq_sum]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr card_lowerRamificationGroup_zero_pos).le
    calc u = (if (1 : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 then
          enatMin (lowerIndex K L 1 - 1) u else 0) := by
          simp [(lowerRamificationGroup K L 0).one_mem]
      _ ≤ _ := Finset.single_le_sum (f := fun σ : L ≃ₐ[K] L ↦
          if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) u else 0)
          (fun σ _ ↦ by
            split_ifs
            · exact enatMin_nonneg _ hu
            · exact le_rfl) (Finset.mem_univ 1)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono hge)
    (Tendsto.const_mul_atTop (inv_pos.mpr card_lowerRamificationGroup_zero_pos) tendsto_id)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tendsto_herbrandPhi_atBot : Tendsto (herbrandPhi K L) atBot atBot :=
  tendsto_id.congr' ((eventually_le_atBot 0).mono fun _ hu ↦ (herbrandPhi_of_nonpos hu).symm)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPhi_surjective : Function.Surjective (herbrandPhi K L) :=
  continuous_herbrandPhi.surjective tendsto_herbrandPhi_atTop tendsto_herbrandPhi_atBot

variable (K L) in

def herbrandPhiOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (herbrandPhi K L) herbrandPhi_strictMono herbrandPhi_surjective

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem herbrandPhiOrderIso_apply (u : ℝ) : herbrandPhiOrderIso K L u = herbrandPhi K L u :=
  rfl

variable (K L) in

def herbrandPsi (v : ℝ) : ℝ :=
  (herbrandPhiOrderIso K L).symm v

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPhi_herbrandPsi (v : ℝ) : herbrandPhi K L (herbrandPsi K L v) = v :=
  (herbrandPhiOrderIso K L).apply_symm_apply v

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPsi_herbrandPhi (u : ℝ) : herbrandPsi K L (herbrandPhi K L u) = u :=
  (herbrandPhiOrderIso K L).symm_apply_apply u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPsi_strictMono : StrictMono (herbrandPsi K L) :=
  (herbrandPhiOrderIso K L).symm.strictMono

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.
-/
theorem herbrandPsi_eq_iff {u v : ℝ} : herbrandPsi K L v = u ↔ herbrandPhi K L u = v := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPsi_of_nonpos {v : ℝ} (hv : v ≤ 0) : herbrandPsi K L v = v :=
  herbrandPsi_eq_iff.mpr (herbrandPhi_of_nonpos hv)

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem herbrandPsi_zero : herbrandPsi K L 0 = 0 :=
  herbrandPsi_of_nonpos le_rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem relIndex_pos_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    (0 : ℝ) < H.relIndex K := by
  have h := relIndex_mul_card_inf H K
  have hK : 0 < Nat.card K := Nat.card_pos
  have : 0 < H.relIndex K := by
    rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | h0
    · rw [h0, zero_mul] at h; omega
    · exact h0
  exact_mod_cast this

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable.

Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herbrandPhi_of_mem_Icc (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (n : ℝ) (n + 1)) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) / ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup K L 0) : ℝ) := by
  classical
  have hG : lowerRamificationGroup K L ((n : ℤ) + 1) = lowerRamificationGroupReal K L ((n : ℝ) + 1) := by
    rw [← lowerRamificationGroupReal_intCast]
    push_cast
    rfl
  have h : ∀ σ : L ≃ₐ[K] L, (if σ ∈ lowerRamificationGroup K L 0 then
      enatMin (lowerIndex K L σ - 1) u else 0) =
        (if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) n else 0) +
          (u - n) * if σ ∈ lowerRamificationGroup K L 0 ∧
            σ ∈ lowerRamificationGroupReal K L ((n : ℝ) + 1) then 1 else 0 := by
    intro σ
    by_cases h0 : σ ∈ lowerRamificationGroup K L 0
    · simp only [h0, true_and, if_true]
      have h1 := one_le_lowerIndex_iff.mpr h0
      generalize hn : lowerIndex K L σ = N at h1
      induction N using ENat.recTopCoe with
      | top =>
        have : σ ∈ lowerRamificationGroupReal K L ((n : ℝ) + 1) := by
          rw [mem_lowerRamificationGroupReal_iff, hn, enatMin_top]
        simp [this]
      | coe m =>
        have hm : 1 ≤ m := by exact_mod_cast h1
        rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hn, ← ENat.natCast_one,
          ← ENat.natCast_sub, enatMin_coe, enatMin_coe, Nat.cast_sub hm, Nat.cast_one]
        by_cases hmn : (n : ℝ) + 1 + 1 ≤ m
        · rw [if_pos hmn, min_eq_right (by linarith [hu.2]), min_eq_right (by linarith)]
          ring
        · rw [if_neg hmn]
          have hmn' : (m : ℝ) - 1 ≤ n := by
            have : m < n + 2 := by exact_mod_cast (show (m : ℝ) < n + 2 by linarith)
            have : (m : ℝ) ≤ n + 1 := by exact_mod_cast (show m ≤ n + 1 by omega)
            linarith
          rw [min_eq_left hmn', min_eq_left (hmn'.trans hu.1)]
          ring
    · simp [h0]
  rw [herbrandPhi_eq_sum, herbrandPhi_eq_sum]
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hG, div_eq_mul_inv, inv_relIndex_eq_sum]
  ring

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem herbrandPsi_of_mem_Icc (n : ℕ) {v : ℝ}
    (hv : v ∈ Set.Icc (herbrandPhi K L n) (herbrandPhi K L (n + 1))) :
    herbrandPsi K L v = n + (v - herbrandPhi K L n) *
      ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup K L 0) : ℝ) := by
  set u := herbrandPsi K L v with hu_def
  have hu : u ∈ Set.Icc (n : ℝ) (n + 1) := by
    constructor
    · rw [← herbrandPsi_herbrandPhi (K := K) (L := L) (n : ℝ)]
      exact (herbrandPsi_strictMono (K := K) (L := L)).monotone hv.1
    · rw [← herbrandPsi_herbrandPhi (K := K) (L := L) ((n : ℝ) + 1)]
      exact (herbrandPsi_strictMono (K := K) (L := L)).monotone hv.2
  have h := herbrandPhi_of_mem_Icc (K := K) (L := L) n hu
  rw [hu_def, herbrandPhi_herbrandPsi] at h
  have hr := relIndex_pos_of_finite (lowerRamificationGroup K L ((n : ℤ) + 1))
    (lowerRamificationGroup K L 0)
  rw [h]
  field_simp
  ring

variable (K L) in

def upperRamificationGroup (v : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  lowerRamificationGroupReal K L (herbrandPsi K L v)

@[simp]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem upperRamificationGroup_herbrandPhi (u : ℝ) :
    upperRamificationGroup K L (herbrandPhi K L u) = lowerRamificationGroupReal K L u := by
  rw [upperRamificationGroup, herbrandPsi_herbrandPhi]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem upperRamificationGroup_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L v := by
  rw [upperRamificationGroup, herbrandPsi_of_nonpos hv]

@[simp]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem upperRamificationGroup_zero :
    upperRamificationGroup K L 0 = lowerRamificationGroup K L 0 := by
  rw [upperRamificationGroup_of_nonpos le_rfl, ← Nat.cast_zero, lowerRamificationGroupReal_natCast,
    Nat.cast_zero]

variable (K L) in

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) :=
  fun _ _ h ↦ lowerRamificationGroupReal_antitone K L (herbrandPsi_strictMono.monotone h)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_upperRamificationGroup_iff_of_lowerIndex_eq {v : ℝ} {σ : L ≃ₐ[K] L} {m : ℕ}
    (h : lowerIndex K L σ = m) :
    σ ∈ upperRamificationGroup K L v ↔ v ≤ herbrandPhi K L ((m : ℝ) - 1) := by
  rw [upperRamificationGroup, mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq h,
    ← le_sub_iff_add_le, ← (herbrandPhi_strictMono (K := K) (L := L)).le_iff_le,
    herbrandPhi_herbrandPsi]

end

end GroundTheory.LocalField
