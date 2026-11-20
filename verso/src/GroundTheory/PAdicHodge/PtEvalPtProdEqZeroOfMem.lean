import Mathlib
import GroundTheory.PAdicHodge.IsUnitAnnResOfMultEqZero
import GroundTheory.PAdicHodge.ExtRobbaBezout
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} [CompleteSpace L] [IsAlgClosed L]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Rewrite using `[ptProd_nil, T.mult_one hr]`. Both sides reduce to the same expression. Consider the case `cons P l ih`.

Rewrite using `[ptProd_cons, T.mult_mul (T.ptExt_ne_zero P.2) (T.ptProd_ne_zero l) hr, T.mult_ptExt P.2 hr, if_pos (hl P List.mem_cons_self).symm, ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_ptProd (l : List T.Pt) {r : ℝ} (hr : 0 < r ∧ r < ρ0) (hl : ∀ P ∈ l, T.ptRad P.1 = r) :
    T.mult (T.ptProd ρ0 l) r = l.length := by
  induction l with
  | nil =>
    rw [ptProd_nil, T.mult_one hr]; rfl
  | cons P l ih =>
    rw [ptProd_cons, T.mult_mul (T.ptExt_ne_zero P.2) (T.ptProd_ne_zero l) hr,
      T.mult_ptExt P.2 hr, if_pos (hl P List.mem_cons_self).symm,
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons]
    push_cast; ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rw [ptProd_nil, extNorm_one]`. Simplify using the standard rewrite rules. Consider the case `cons P l ih`. Rewrite using `[ptProd_cons, extNorm_mul, T.extNorm_ξExt P.2, max_eq_right (hl P List.mem_cons_self), ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem extNorm_ptProd (l : List T.Pt) (s : Set.Ioc (0 : ℝ) ρ0) (hl : ∀ P ∈ l, T.ptRad P.1 ≤ s) :
    T.extNorm ρ0 s (T.ptProd ρ0 l) = (s : ℝ) ^ l.length := by
  induction l with
  | nil => rw [ptProd_nil, extNorm_one]; simp
  | cons P l ih =>
    rw [ptProd_cons, extNorm_mul, T.extNorm_ξExt P.2, max_eq_right (hl P List.mem_cons_self),
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ), List.length_cons, pow_succ]; ring

def intEval {ξ : T.int} (hξ : T.IsPrimOne ξ) : T.int →+* T.UntiltField hξ :=
  (T.toUntiltField hξ).comp (T.toUntilt ξ)

/- English proof (translation)
The claim follows from `(T.ptE_int hξ X.2).symm`.
-/
theorem intEval_apply {ξ : T.int} (hξ : T.IsPrimOne ξ) (X : T.int) :
    T.intEval hξ X = T.ptE hξ (X : Γ) := (T.ptE_int hξ X.2).symm

/- English proof (translation)
Rewrite using `[intEval, RingHom.comp_apply, norm_toUntiltField]`. Conclude with `T.untiltNorm_le_one hξ _`.
-/
theorem norm_intEval_le_one {ξ : T.int} (hξ : T.IsPrimOne ξ) (X : T.int) : ‖T.intEval hξ X‖ ≤ 1 := by
  rw [intEval, RingHom.comp_apply, norm_toUntiltField]; exact T.untiltNorm_le_one hξ _

/- English proof (translation)
Establish `hr1` using `T.ptRad_lt_one' P.2`. Establish `hw1 : ‖T.ptE P.2 (Q.1 : Γ)‖ ≤ 1` using `hv.trans (hδ.trans hr1).le`. Take `⟨z, hz, V, hV, hzV⟩` from `T.exists_lift_value P.2 hw1`. Establish `hz1 : ‖z‖ ≤ 1` using `hz ▸ hw1`. Use `set W : T.int := ⟨T.teich z * V, T.int.mul_mem (T.teich_mem_int hz1) hV⟩`.

Establish `h0 : T.toUntilt P.1 (Q.1 - W) = 0`. Rewrite using `[← T.toUntiltField_eq_zero_iff P]`. Express the relevant statement in the definitionally equal form `T.intEval P.2 (Q.1 - W) = 0`. Rewrite using `[map_sub, intEval_apply, intEval_apply]`. Use `show T.ptE P.2 (Q.1 : Γ) - T.ptE P.2 (T.teich z * V) = 0`.

Rewrite using `[hzV, sub_self]`. Take `⟨B, hB, hQB⟩` from `(T.toUntilt_eq_zero_iff).1 h0`. Use `⟨⟨B, hB⟩, z, V, ?_, hz ▸ hv, hV, ?_⟩` and prove the remaining obligations. Rewrite using `[T.isUnit_int_iff]`. Establish `hred : T.red (Q.1 : Γ) = T.red (P.1 : Γ) * T.red B + z * T.red V`.

Establish `: (Q.1 : Γ) = P.1 * B + T.teich z * V`. Establish `h` using `hQB`. Simplify using `only [AddSubgroupClass.coe_sub] at h`. Rewrite `h` using `[show (W : Γ) = T.teich z * V from rfl]`. Take the linear combination `h`.

Rewrite using `[this, map_add, map_mul, map_mul, red_teich]`. Establish `hQ : ‖T.red (Q.1 : Γ)‖ = T.ptRad P.1` using `by rw [← coeff_zero, ← hrad]; rfl`. Establish `hP : ‖T.red (P.1 : Γ)‖ = T.ptRad P.1` using `by rw [← coeff_zero]; rfl`. Establish `hzV' : ‖z * T.red V‖ < T.ptRad P.1`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hPB : ‖T.red (P.1 : Γ) * T.red B‖ = T.ptRad P.1`. Establish `e : T.red (P.1 : Γ) * T.red B = T.red (Q.1 : Γ) - z * T.red V` using `by rw [hred]; ring`. Rewrite using `[e, ultra_norm_sub_eq_left (by rw [hQ]; exact hzV'), hQ]`. Rewrite `hPB` using `[norm_mul, hP]`.

Establish `hr0` using `T.ptRad_pos' P.2`. Clear denominators, using `at hPB` for the nonvanishing conditions. Combine the linear relations using `[hPB]`. Establish `h` using `hQB`. Simplify using `only [AddSubgroupClass.coe_sub] at h`.

Rewrite `h` using `[show (W : Γ) = T.teich z * V from rfl]`. Use `show (Q.1 : Γ) = P.1 * B + T.teich z * V`. Take the linear combination `h`.
-/
theorem exists_step_pt {P Q : T.Pt} {δ : ℝ} (hrad : T.ptRad Q.1 = T.ptRad P.1) (hδ : δ < T.ptRad P.1)
    (hv : ‖T.ptE P.2 (Q.1 : Γ)‖ ≤ δ) :
    ∃ (q : T.int) (z : L) (V : Γ), IsUnit q ∧ ‖z‖ ≤ δ ∧ V ∈ T.int ∧
      (Q.1 : Γ) = P.1 * q + T.teich z * V := by
  have hr1 := T.ptRad_lt_one' P.2
  have hw1 : ‖T.ptE P.2 (Q.1 : Γ)‖ ≤ 1 := hv.trans (hδ.trans hr1).le
  obtain ⟨z, hz, V, hV, hzV⟩ := T.exists_lift_value P.2 hw1
  have hz1 : ‖z‖ ≤ 1 := hz ▸ hw1
  set W : T.int := ⟨T.teich z * V, T.int.mul_mem (T.teich_mem_int hz1) hV⟩
  have h0 : T.toUntilt P.1 (Q.1 - W) = 0 := by
    rw [← T.toUntiltField_eq_zero_iff P]
    change T.intEval P.2 (Q.1 - W) = 0
    rw [map_sub, intEval_apply, intEval_apply]
    show T.ptE P.2 (Q.1 : Γ) - T.ptE P.2 (T.teich z * V) = 0
    rw [hzV, sub_self]
  obtain ⟨B, hB, hQB⟩ := (T.toUntilt_eq_zero_iff).1 h0
  refine ⟨⟨B, hB⟩, z, V, ?_, hz ▸ hv, hV, ?_⟩
  · rw [T.isUnit_int_iff]
    have hred : T.red (Q.1 : Γ) = T.red (P.1 : Γ) * T.red B + z * T.red V := by
      have : (Q.1 : Γ) = P.1 * B + T.teich z * V := by
        have h := hQB
        simp only [AddSubgroupClass.coe_sub] at h
        rw [show (W : Γ) = T.teich z * V from rfl] at h
        linear_combination h
      rw [this, map_add, map_mul, map_mul, red_teich]
    have hQ : ‖T.red (Q.1 : Γ)‖ = T.ptRad P.1 := by rw [← coeff_zero, ← hrad]; rfl
    have hP : ‖T.red (P.1 : Γ)‖ = T.ptRad P.1 := by rw [← coeff_zero]; rfl
    have hzV' : ‖z * T.red V‖ < T.ptRad P.1 := by
      rw [norm_mul]
      calc ‖z‖ * ‖T.red V‖ ≤ δ * 1 :=
            mul_le_mul (hz ▸ hv) (T.norm_red_le_one V hV) (norm_nonneg _) ((norm_nonneg _).trans (hz ▸ hv))
        _ < T.ptRad P.1 := by rw [mul_one]; exact hδ
    have hPB : ‖T.red (P.1 : Γ) * T.red B‖ = T.ptRad P.1 := by
      have e : T.red (P.1 : Γ) * T.red B = T.red (Q.1 : Γ) - z * T.red V := by rw [hred]; ring
      rw [e, ultra_norm_sub_eq_left (by rw [hQ]; exact hzV'), hQ]
    rw [norm_mul, hP] at hPB
    have hr0 := T.ptRad_pos' P.2
    field_simp at hPB
    linarith [hPB]
  · have h := hQB
    simp only [AddSubgroupClass.coe_sub] at h
    rw [show (W : Γ) = T.teich z * V from rfl] at h
    show (Q.1 : Γ) = P.1 * B + T.teich z * V
    linear_combination h

/- English proof (translation)
Establish `hr0 : 0 < r` using `hr 0 ▸ T.ptRad_pos' (hξ 0)`. Establish `hr1 : r < 1` using `hr 0 ▸ T.ptRad_lt_one' (hξ 0)`. Establish `hB0 : ∀ J, 0 ≤ B J` using `fun J => (norm_nonneg _).trans (hzB J)`. Use `set u : ℕ → (T.int)ˣ := fun J => ∏ i ∈ Finset.range J, (hq i).unit with hudef`. Establish `hu0 : u 0 = 1` using `by simp [hudef]`.

Establish `husucc : ∀ J, u (J + 1) = u J * (hq J).unit` using `fun J => by simp [hudef, Finset.prod_range_succ]`. Use `set η : ℕ → Γ := fun J => (ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) with hηdef`. Establish `hηint : ∀ J, η J ∈ T.int` using `fun J => T.int.mul_mem (ξ J).2 (((u J)⁻¹ : (T.int)ˣ) : T.int).2`. Use `set W : ℕ → Γ := fun J => V J * ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) with hWdef`. Establish `hWint : ∀ J, W J ∈ T.int` using `fun J => T.int.mul_mem (hV J) (((u (J + 1))⁻¹ : (T.int)ˣ) : T.int).2`.

Establish `hdiff : ∀ J, η (J + 1) - η J = T.teich (z J) * W J`. Introduce `J`. Establish `h1 : ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) = ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ)`. Rewrite using `[husucc, mul_inv_rev, Units.val_mul, Subring.coe_mul, mul_comm]`. Establish `h2 : ((q J : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ) = 1`.

Rewrite using `[← Subring.coe_mul]`. Establish `: (q J : T.int) * ((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) = 1` using `(hq J).mul_val_inv`. Rewrite using `[this]`. Both sides reduce to the same expression. Simplify using `only [hηdef, hWdef, hstep J, h1]`.

Take the linear combination `((ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ)) * h2`. Establish `hconv : ∀ X : Γ, X ∈ T.int → ConvergesAt (T.zcoeff X) r` using `fun X hX => T.convergesAt_of_mem_int hX hr0 hr1`. Establish `hinc : ∀ J, gaussNorm (T.zcoeff (η (J + 1) - η J)) r ≤ B J`. Introduce `J`. Rewrite using `[hdiff J]`.

Conclude with `(T.gaussNorm_teich_mul_int_le (hWint J) hr0 hr1).trans (hzB J)`. Establish `hbound : ∀ J K, J ≤ K → gaussNorm (T.zcoeff (η K - η J)) r ≤ B J`. Introduce `J K hJK`. Proceed by induction on `K, hJK using Nat.le_induction with`. Consider the case `base => rw [sub_self, (T.zcoeff_eq_zero_iff 0).2 rfl]`.

Simplify `hB0 J` using `[gaussNorm]`. Consider the case `succ K hK ih`. Establish `e : η (K + 1) - η J = (η (K + 1) - η K) + (η K - η J)` using `by ring`. Rewrite using `[e]`. Use `(T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _))) (hconv _ (sub_mem (hηint _) (hηint _)))).trans (max_le ((hinc K).trans (hBanti hK)) ih)` and prove the remaining obligations.

Establish `hsymm : ∀ J K, gaussNorm (T.zcoeff (η K - η J)) r ≤ B (min J K)`. Introduce `J K`. Break down `le_total J K with h | h` into its components or cases. Rewrite using `[min_eq_left h]`. Conclude with `hbound J K h`.

Rewrite using `[min_eq_right h, ← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]`. Conclude with `hbound K J h`. Take `⟨hcoef, hLconv, hlim⟩` from `T.exists_limit_gaussNorm hr0 hr1 (x := η) (fun k => hconv _ (hηint k)) (fun ε hε => by`. Take `⟨N, hN⟩` from `eventually_atTop.1 (hBlim.eventually (ge_mem_nhds hε))`. Conclude with `⟨N, fun k hk l hl => by`.

Rewrite using `[← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]`. Conclude with `(hsymm k l).trans (hN _ (le_min hk hl))⟩)`. Use `set ηL := T.coeffLim η`. Establish `hLint : ηL ∈ T.int` using `T.mem_int_iff.2 fun n => le_of_tendsto ((continuous_norm.tendsto _).comp (T.tendsto_coeff_coeffLim hcoef n)) (Eventually.of_forall fun k => T.mem_int_iff.1 (hηint k) n)`. Use `set Y : Γ := η 0 - ηL`.

Establish `hYint : Y ∈ T.int` using `sub_mem (hηint 0) hLint`. Establish `hYg : gaussNorm (T.zcoeff Y) r ≤ B 0`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Take `⟨N, hN⟩` from `hlim ε hε`. Establish `e : Y = (η 0 - η N) + (η N - ηL)` using `by simp only [Y]; ring`.

Rewrite using `[e]`. Use `(T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _))) (hconv _ (sub_mem (hηint _) hLint))).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]`. Conclude with `(hbound 0 N (Nat.zero_le _)).trans (le_add_of_nonneg_right hε.le)`. Conclude with `(hN N le_rfl).trans (le_add_of_nonneg_left (hB0 0))`.

Establish `hweight : ∀ m : ℕ, ‖T.coeff Y m‖ * r ^ m ≤ B 0` using `fun m => by`. Use `(hconv Y hYint).le_gaussNorm m` as an intermediate fact. Rewrite `this` using `[zcoeff_natCast, zpow_natCast]`. Conclude with `this.trans hYg`. Establish `hpre` using `T.prefixLe_of_weight hr0 hr1.le hweight 1`.

Rewrite `hpre` using `[pow_one]`. Establish `hδ0 : 0 ≤ B 0 / r` using `div_nonneg (hB0 0) hr0.le`. Establish `hδ : B 0 / r < T.ptRad (ξ 0)`. Rewrite using `[hr 0, div_lt_iff₀ hr0]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hη0 : η 0 = (ξ 0 : Γ)` using `by simp [hηdef, hu0]`. Take `⟨hηL, hradL⟩` from `T.isPrimOne_sub_of_prefix (hξ 0) (Y := ⟨Y, hYint⟩) hδ0 hδ hpre`. Use `set ηp : T.int := ξ 0 - ⟨Y, hYint⟩`. Establish `hηp : (ηp : Γ) = ηL` using `by show (ξ 0 : Γ) - Y = ηL`. Simplify using `only [Y, hη0]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨ηp, hηL, hradL.trans (hr 0), ?_⟩` and prove the remaining obligations. Establish `hval : ∀ J, ‖T.ptE hηL ((ξ J : T.int) : Γ)‖ ≤ gaussNorm (T.zcoeff (η J - ηL)) r`. Introduce `J`. Establish `hξJ : ξ J = ⟨η J, hηint J⟩ * ((u J : (T.int)ˣ) : T.int)` using `Subtype.ext (by`.

Simplify using `only [hηdef, Subring.coe_mul]`. Rewrite using `[mul_assoc, ← Subring.coe_mul, Units.inv_mul]`. Use the proof step `simp)`. Establish `hη : (⟨η J, hηint J⟩ : T.int) = ηp + ⟨η J - ηL, sub_mem (hηint J) hLint⟩` using `Subtype.ext (by simp only [Subring.coe_add, hηp]; ring)`. Rewrite using `[← intEval_apply, hξJ, map_mul, norm_mul, hη, map_add, intEval_apply, intEval_apply]`.

Rewrite using `[show ((ηp : T.int) : Γ) = ηp from rfl, T.ptE_ξ hηL, zero_add]`. Use `(mul_le_of_le_one_right (norm_nonneg _) (T.norm_intEval_le_one hηL _)).trans ?_` and prove the remaining obligations. Use `(T.norm_ptE_le hηL ?_).trans ?_` and prove the remaining obligations. Rewrite using `[hradL, hr 0]`. Conclude with `hconv _ (sub_mem (hηint J) hLint)`.

Rewrite using `[hradL, hr 0]`. Use `squeeze_zero (fun J => norm_nonneg _) hval ?_` and prove the remaining obligations. Rewrite using `[Metric.tendsto_atTop]`. Introduce `ε hε`. Take `⟨N, hN⟩` from `hlim (ε / 2) (half_pos hε)`.

Use `⟨N, fun J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg hr0)]`. Conclude with `(hN J hJ).trans_lt (half_lt_self hε)`.
-/
theorem exists_limit_pt {r : ℝ} (ξ : ℕ → T.int) (hξ : ∀ J, T.IsPrimOne (ξ J)) (hr : ∀ J, T.ptRad (ξ J) = r)
    (q : ℕ → T.int) (hq : ∀ J, IsUnit (q J)) (z : ℕ → L) (V : ℕ → Γ) (hV : ∀ J, V J ∈ T.int)
    (hstep : ∀ J, ((ξ (J + 1) : T.int) : Γ) = ξ J * q J + T.teich (z J) * V J)
    (B : ℕ → ℝ) (hBanti : Antitone B) (hBlim : Tendsto B atTop (𝓝 0)) (hzB : ∀ J, ‖z J‖ ≤ B J)
    (hBr : B 0 < r ^ 2) :
    ∃ (η : T.int) (hη : T.IsPrimOne η), T.ptRad η = r ∧
      Tendsto (fun J => ‖T.ptE hη ((ξ J : T.int) : Γ)‖) atTop (𝓝 0) := by
  have hr0 : 0 < r := hr 0 ▸ T.ptRad_pos' (hξ 0)
  have hr1 : r < 1 := hr 0 ▸ T.ptRad_lt_one' (hξ 0)
  have hB0 : ∀ J, 0 ≤ B J := fun J => (norm_nonneg _).trans (hzB J)

  set u : ℕ → (T.int)ˣ := fun J => ∏ i ∈ Finset.range J, (hq i).unit with hudef
  have hu0 : u 0 = 1 := by simp [hudef]
  have husucc : ∀ J, u (J + 1) = u J * (hq J).unit := fun J => by simp [hudef, Finset.prod_range_succ]
  set η : ℕ → Γ := fun J => (ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) with hηdef
  have hηint : ∀ J, η J ∈ T.int := fun J => T.int.mul_mem (ξ J).2 (((u J)⁻¹ : (T.int)ˣ) : T.int).2
  set W : ℕ → Γ := fun J => V J * ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) with hWdef
  have hWint : ∀ J, W J ∈ T.int := fun J => T.int.mul_mem (hV J) (((u (J + 1))⁻¹ : (T.int)ˣ) : T.int).2
  have hdiff : ∀ J, η (J + 1) - η J = T.teich (z J) * W J := by
    intro J
    have h1 : ((((u (J + 1))⁻¹ : (T.int)ˣ) : T.int) : Γ) =
        ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ) := by
      rw [husucc, mul_inv_rev, Units.val_mul, Subring.coe_mul, mul_comm]
    have h2 : ((q J : T.int) : Γ) * (((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) : Γ) = 1 := by
      rw [← Subring.coe_mul]
      have : (q J : T.int) * ((((hq J).unit)⁻¹ : (T.int)ˣ) : T.int) = 1 := (hq J).mul_val_inv
      rw [this]; rfl
    simp only [hηdef, hWdef, hstep J, h1]
    linear_combination ((ξ J : Γ) * ((((u J)⁻¹ : (T.int)ˣ) : T.int) : Γ)) * h2
  have hconv : ∀ X : Γ, X ∈ T.int → ConvergesAt (T.zcoeff X) r := fun X hX =>
    T.convergesAt_of_mem_int hX hr0 hr1
  have hinc : ∀ J, gaussNorm (T.zcoeff (η (J + 1) - η J)) r ≤ B J := by
    intro J
    rw [hdiff J]
    exact (T.gaussNorm_teich_mul_int_le (hWint J) hr0 hr1).trans (hzB J)
  have hbound : ∀ J K, J ≤ K → gaussNorm (T.zcoeff (η K - η J)) r ≤ B J := by
    intro J K hJK
    induction K, hJK using Nat.le_induction with
    | base => rw [sub_self, (T.zcoeff_eq_zero_iff 0).2 rfl]; simpa [gaussNorm] using hB0 J
    | succ K hK ih =>
      have e : η (K + 1) - η J = (η (K + 1) - η K) + (η K - η J) := by ring
      rw [e]
      refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _)))
        (hconv _ (sub_mem (hηint _) (hηint _)))).trans (max_le ((hinc K).trans (hBanti hK)) ih)
  have hsymm : ∀ J K, gaussNorm (T.zcoeff (η K - η J)) r ≤ B (min J K) := by
    intro J K
    rcases le_total J K with h | h
    · rw [min_eq_left h]; exact hbound J K h
    · rw [min_eq_right h, ← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
      exact hbound K J h
  obtain ⟨hcoef, hLconv, hlim⟩ := T.exists_limit_gaussNorm hr0 hr1 (x := η) (fun k => hconv _ (hηint k))
    (fun ε hε => by
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hBlim.eventually (ge_mem_nhds hε))
      exact ⟨N, fun k hk l hl => by
        rw [← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
        exact (hsymm k l).trans (hN _ (le_min hk hl))⟩)
  set ηL := T.coeffLim η
  have hLint : ηL ∈ T.int := T.mem_int_iff.2 fun n =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (T.tendsto_coeff_coeffLim hcoef n))
      (Eventually.of_forall fun k => T.mem_int_iff.1 (hηint k) n)
  set Y : Γ := η 0 - ηL
  have hYint : Y ∈ T.int := sub_mem (hηint 0) hLint
  have hYg : gaussNorm (T.zcoeff Y) r ≤ B 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hlim ε hε
    have e : Y = (η 0 - η N) + (η N - ηL) := by simp only [Y]; ring
    rw [e]
    refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le (hconv _ (sub_mem (hηint _) (hηint _)))
      (hconv _ (sub_mem (hηint _) hLint))).trans (max_le ?_ ?_)
    · rw [← neg_sub, T.gaussNorm_zcoeff_neg hr0 hr1 (hconv _ (sub_mem (hηint _) (hηint _)))]
      exact (hbound 0 N (Nat.zero_le _)).trans (le_add_of_nonneg_right hε.le)
    · exact (hN N le_rfl).trans (le_add_of_nonneg_left (hB0 0))
  have hweight : ∀ m : ℕ, ‖T.coeff Y m‖ * r ^ m ≤ B 0 := fun m => by
    have := (hconv Y hYint).le_gaussNorm m
    rw [zcoeff_natCast, zpow_natCast] at this
    exact this.trans hYg
  have hpre := T.prefixLe_of_weight hr0 hr1.le hweight 1
  rw [pow_one] at hpre
  have hδ0 : 0 ≤ B 0 / r := div_nonneg (hB0 0) hr0.le
  have hδ : B 0 / r < T.ptRad (ξ 0) := by
    rw [hr 0, div_lt_iff₀ hr0]; nlinarith
  have hη0 : η 0 = (ξ 0 : Γ) := by simp [hηdef, hu0]
  obtain ⟨hηL, hradL⟩ := T.isPrimOne_sub_of_prefix (hξ 0) (Y := ⟨Y, hYint⟩) hδ0 hδ hpre
  set ηp : T.int := ξ 0 - ⟨Y, hYint⟩
  have hηp : (ηp : Γ) = ηL := by
    show (ξ 0 : Γ) - Y = ηL
    simp only [Y, hη0]; ring
  refine ⟨ηp, hηL, hradL.trans (hr 0), ?_⟩

  have hval : ∀ J, ‖T.ptE hηL ((ξ J : T.int) : Γ)‖ ≤ gaussNorm (T.zcoeff (η J - ηL)) r := by
    intro J
    have hξJ : ξ J = ⟨η J, hηint J⟩ * ((u J : (T.int)ˣ) : T.int) := Subtype.ext (by
      simp only [hηdef, Subring.coe_mul]
      rw [mul_assoc, ← Subring.coe_mul, Units.inv_mul]; simp)
    have hη : (⟨η J, hηint J⟩ : T.int) = ηp + ⟨η J - ηL, sub_mem (hηint J) hLint⟩ :=
      Subtype.ext (by simp only [Subring.coe_add, hηp]; ring)
    rw [← intEval_apply, hξJ, map_mul, norm_mul, hη, map_add, intEval_apply, intEval_apply]
    rw [show ((ηp : T.int) : Γ) = ηp from rfl, T.ptE_ξ hηL, zero_add]
    refine (mul_le_of_le_one_right (norm_nonneg _) (T.norm_intEval_le_one hηL _)).trans ?_
    refine (T.norm_ptE_le hηL ?_).trans ?_
    · rw [hradL, hr 0]; exact hconv _ (sub_mem (hηint J) hLint)
    · rw [hradL, hr 0]
  refine squeeze_zero (fun J => norm_nonneg _) hval ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun J hJ => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg hr0)]
  exact (hN J hJ).trans_lt (half_lt_self hε)

/- English proof (translation)
Establish `hc0` using `T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)`. Establish `hc'0` using `T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc' _)`. Establish `hr0 : 0 < r` using `σ0.2.1.trans hr`. Establish `key : ∀ σ : Set.Ioc (0 : ℝ) ρ0, r ≤ σ → (σ : ℝ) ≤ ρ0 → gaussNorm (T.coeffB ((c' : T.B) - c)) σ < gaussNorm (T.coeffB (c : T.B)) σ`. Introduce `σ h1 h2`.

Use `set s : AnnRad ρ0 σ0 := ⟨σ, hr.le.trans h1, h2⟩`. Establish `e1 : gaussNorm (T.coeffB ((c' : T.B) - c)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c' - T.coeAnn c)`. Rewrite using `[← map_sub, annNorm_coeAnn]`. Both sides reduce to the same expression. Establish `e2 : gaussNorm (T.coeffB (c : T.B)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c)`.

Rewrite using `[annNorm_coeAnn]`. Rewrite using `[e1, e2, T.annNorm_eq_of_sub_lt (hc s)]`. Establish `e3 : T.coeAnn c' - T.coeAnn c = (v - T.coeAnn c) - (v - T.coeAnn c')` using `by ring`. Rewrite using `[e3]`. Conclude with `(T.annNorm_sub_le s _ _).trans_lt (max_lt (hc s) (hc' s))`.

Take `⟨hl, hh⟩` from `T.idx_eq_of_lt (c := c) (c' := c') hr0 hrρ le_rfl key`. Establish `h : 0 < r ∧ r < ρ0` using `⟨hr0, hrρ⟩`. Rewrite using `[mult, mult, (T.idx_coe hc0 h).1, (T.idx_coe hc0 h).2, (T.idx_coe hc'0 h).1, (T.idx_coe hc'0 h).2, hl, hh]`.
-/
theorem mult_eq_of_approx_ann {v : T.Ann ρ0 σ0} {c c' : T.Econ ρ0}
    (hc : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c) < T.annNorm ρ0 σ0 s v)
    (hc' : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c') < T.annNorm ρ0 σ0 s v) {r : ℝ} (hr : (σ0 : ℝ) < r)
    (hrρ : r < ρ0) : T.mult (c : T.RobbaExt ρ0) r = T.mult (c' : T.RobbaExt ρ0) r := by
  have hc0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc _)
  have hc'0 := T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hc' _)
  have hr0 : 0 < r := σ0.2.1.trans hr
  have key : ∀ σ : Set.Ioc (0 : ℝ) ρ0, r ≤ σ → (σ : ℝ) ≤ ρ0 →
      gaussNorm (T.coeffB ((c' : T.B) - c)) σ < gaussNorm (T.coeffB (c : T.B)) σ := by
    intro σ h1 h2
    set s : AnnRad ρ0 σ0 := ⟨σ, hr.le.trans h1, h2⟩
    have e1 : gaussNorm (T.coeffB ((c' : T.B) - c)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c' - T.coeAnn c) := by
      rw [← map_sub, annNorm_coeAnn]; rfl
    have e2 : gaussNorm (T.coeffB (c : T.B)) σ = T.annNorm ρ0 σ0 s (T.coeAnn c) := by
      rw [annNorm_coeAnn]
    rw [e1, e2, T.annNorm_eq_of_sub_lt (hc s)]
    have e3 : T.coeAnn c' - T.coeAnn c = (v - T.coeAnn c) - (v - T.coeAnn c') := by ring
    rw [e3]
    exact (T.annNorm_sub_le s _ _).trans_lt (max_lt (hc s) (hc' s))
  obtain ⟨hl, hh⟩ := T.idx_eq_of_lt (c := c) (c' := c') hr0 hrρ le_rfl key
  have h : 0 < r ∧ r < ρ0 := ⟨hr0, hrρ⟩
  rw [mult, mult, (T.idx_coe hc0 h).1, (T.idx_coe hc0 h).2, (T.idx_coe hc'0 h).1, (T.idx_coe hc'0 h).2,
    hl, hh]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: t ^ l.length ≤ (l.map f).prod` using `by clear h`. Proceed by induction on `l with`. Consider the case `nil => simp`.

Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_comm]`. Conclude with `mul_le_mul (hcon a List.mem_cons_self) (ih fun i hi => hcon i (List.mem_cons_of_mem _ hi)) (pow_nonneg ht _) (hf a)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_lt_of_prod_lt {ι : Type*} (l : List ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {t : ℝ} (ht : 0 ≤ t)
    (h : (l.map f).prod < t ^ l.length) : ∃ i ∈ l, f i < t := by
  by_contra hcon
  push Not at hcon
  have : t ^ l.length ≤ (l.map f).prod := by
    clear h
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_comm]
      exact mul_le_mul (hcon a List.mem_cons_self) (ih fun i hi => hcon i (List.mem_cons_of_mem _ hi))
        (pow_nonneg ht _) (hf a)
  linarith

/- English proof (translation)
Rewrite using `[ptProd, map_list_prod]`. Conclude with `List.prod_eq_zero (List.mem_map.2 ⟨T.ξExt P.1 ρ0, List.mem_map.2 ⟨P, hP, rfl⟩, T.ptEval_ξExt P.2 hr⟩)`.
-/
theorem ptEval_ptProd_eq_zero_of_mem {l : List T.Pt} {P : T.Pt} (hP : P ∈ l) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.ptProd ρ0 l) = 0 := by
  rw [ptProd, map_list_prod]
  exact List.prod_eq_zero (List.mem_map.2 ⟨T.ξExt P.1 ρ0, List.mem_map.2 ⟨P, hP, rfl⟩,
    T.ptEval_ξExt P.2 hr⟩)

/- English proof (translation)
Rewrite using `[T.ptEval_ξExt_eq P hr Q, T.ptE_int P.2 Q.2]`.
-/
theorem ptEval_ξExt_eq_ptE (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) (Q : T.int) :
    T.ptEval P.2 hr (T.ξExt Q ρ0) = T.ptE P.2 (Q : Γ) := by
  rw [T.ptEval_ξExt_eq P hr Q, T.ptE_int P.2 Q.2]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `set m : ℕ := (T.mult (c0 : T.RobbaExt ρ0) r).toNat with hmdef`. Establish `hm' : (m : ℤ) = T.mult (c0 : T.RobbaExt ρ0) r` using `Int.toNat_of_nonneg (by omega)`. Establish `hm1 : 1 ≤ m` using `by omega`. Use `set R : ℝ := (r : ℝ) with hRdef`. Establish `hR0 : 0 < R` using `σ0.2.1.trans hr0`.

Establish `hR1 : R < 1` using `hr1.trans ρ0.2.2`. Use `set Nr := T.annNorm ρ0 σ0 r v with hNrdef`. Establish `hNr : 0 < Nr` using `hv r`. Take `⟨μ, hμ, hμle⟩` from `T.exists_pos_le_annNorm v hv`. Use `set t : ℕ → ℝ := fun J => R ^ 2 / 2 * (1 / 2) ^ J with htdef`.

Establish `ht0 : ∀ J, 0 < t J` using `fun J => by simp only [htdef]; positivity`. Establish `htR : ∀ J, t J < R`. Introduce `J`. Establish `h1 : (1 / 2 : ℝ) ^ J ≤ 1` using `pow_le_one₀ (by norm_num) (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.

Establish `htanti : Antitone t` using `fun J K hJK => by`. Simplify using `only [htdef]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJK) (by positivity)`. Establish `htlim : Tendsto t atTop (𝓝 0)`. Use `(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul (R ^ 2 / 2)` as an intermediate fact.

Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Use `set ε : ℕ → ℝ := fun J => Nr * (t J / R) ^ m with hεdef`. Establish `hε0 : ∀ J, 0 < ε J` using `fun J => mul_pos hNr (pow_pos (div_pos (ht0 J) hR0) m)`. Establish `hεanti : Antitone ε` using `fun J K hJK => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (ht0 K).le hR0.le) (div_le_div_of_nonneg_right (htanti hJK) hR0.le) m) hNr.le`. Establish `hεlim : Tendsto ε atTop (𝓝 0)`.

Establish `h1 : Tendsto (fun J => t J / R) atTop (𝓝 0)` using `by simpa using htlim.div_const R`. Establish `h2` using `(h1.pow m).const_mul Nr`. Rewrite `h2` using `[zero_pow (by omega), mul_zero]`. Then use the resulting hypothesis. Establish `hεt : ∀ J, ε J * R ^ m / Nr = t J ^ m` using `fun J => by`. Simplify using `only [hεdef]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Establish `happ : ∀ J, ∃ c : T.Econ ρ0, ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c) < min (ε J) (μ / 2)` using `fun J => T.exists_coeAnn_near v (lt_min (hε0 J) (half_pos hμ))`. Use `choose c hc using happ`.

Establish `hgood : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < T.annNorm ρ0 σ0 s v` using `fun J s => (hc J s).trans_le ((min_le_right _ _).trans ((half_le_self hμ.le).trans (hμle s)))`. Establish `hcε : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < ε J` using `fun J s => (hc J s).trans_le (min_le_left _ _)`. Establish `hc0' : ∀ J, (c J : T.RobbaExt ρ0) ≠ 0` using `fun J => T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hgood J _)`. Establish `hmJ : ∀ J, T.mult (c J : T.RobbaExt ρ0) R = m` using `fun J => by`. Rewrite using `[hm']`.

Conclude with `(T.mult_eq_of_approx_ann hc0 (hgood J) hr0 hr1).symm`. Establish `hfac : ∀ J, ∃ (l : List T.Pt) (y : T.RobbaExt ρ0), (∀ P ∈ l, R ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ R) ∧ (c J : T.RobbaExt ρ0) = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧ ∀ σ, R ≤ σ → σ ≤ R → T.mult y σ = 0` using `fun J => T.exists_factor_annulus T.rootExists hR0 le_rfl hr1 (hc0' J)`. Use `choose l y hl hcy hy0 hym using hfac`. Establish `hlrad : ∀ J, ∀ P ∈ l J, T.ptRad P.1 = R` using `fun J P hP => le_antisymm (hl J P hP).2 (hl J P hP).1`. Establish `hlen : ∀ J, (l J).length = m`.

Introduce `J`. Establish `h` using `hmJ J`. Rewrite `h` using `[hcy J, T.mult_mul (T.ptProd_ne_zero _) (hy0 J) ⟨hR0, hr1⟩, T.mult_ptProd _ ⟨hR0, hr1⟩ (hlrad J), hym J R le_rfl le_rfl, add_zero]`. Conclude with `h` after adjusting the coercions. Establish `hrIoc : ∀ {ξ : T.int} (hξ : T.IsPrimOne ξ) (hrad : T.ptRad ξ = R), T.ptRadIoc hξ (hrad.trans_le hr1.le) = annIoc r` using `fun hξ hrad => Subtype.ext hrad`.

Establish `hnc : ∀ J, T.extNorm ρ0 (annIoc r) (c J : T.RobbaExt ρ0) = Nr`. Introduce `J`. Rewrite using `[← annNorm_toAnn, toAnn_coe]`. Conclude with `T.annNorm_eq_of_sub_lt (hgood J r)`. Establish `hny : ∀ J, T.extNorm ρ0 (annIoc r) (y J) = Nr / R ^ m`.

Introduce `J`. Establish `h` using `hnc J`. Rewrite `h` using `[hcy J, extNorm_mul, T.extNorm_ptProd _ _ fun P hP => (hlrad J P hP).le, hlen J]`. Establish `hRm : 0 < R ^ m` using `pow_pos hR0 m`. Establish `hc : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = R` using `rfl`.

Rewrite `h` using `[hc]`. Rewrite using `[← h]`. Clear the denominators using the available nonvanishing facts. Establish `hvaly : ∀ J (P : T.Pt) (hP : T.ptRad P.1 = R), ‖T.ptEval P.2 (hP.trans_le hr1.le) (y J)‖ = Nr / R ^ m`. Introduce `J P hP`.

Establish `h` using `T.norm_ptEval_of_mult_eq_zero (hy0 J) P.2 (hP.trans_lt hr1) (by rw [hP]; exact hym J R le_rfl le_rfl)`. Rewrite using `[h, hrIoc P.2 hP, hny]`. Establish `hstep : ∀ J, ∀ P ∈ l J, ∃ Q ∈ l (J + 1), ‖T.ptE P.2 (Q.1 : Γ)‖ < t J`. Introduce `J P hP`. Establish `hPr` using `hlrad J P hP`.

Establish `hPle : T.ptRad P.1 ≤ ρ0` using `hPr.trans_le hr1.le`. Establish `h0 : T.ptEval P.2 hPle (c J : T.RobbaExt ρ0) = 0`. Rewrite using `[hcy J, map_mul, T.ptEval_ptProd_eq_zero_of_mem hP hPle, zero_mul]`. Establish `hsmall : ‖T.ptEval P.2 hPle (c (J + 1) : T.RobbaExt ρ0)‖ < ε J`. Establish `e : (c (J + 1) : T.RobbaExt ρ0) = ((c (J + 1) : T.RobbaExt ρ0) - c J) + c J` using `by ring`.

Rewrite using `[e, map_add, h0, add_zero]`. Use `(T.norm_ptEval_le P.2 hPle _).trans_lt ?_` and prove the remaining obligations. Rewrite using `[hrIoc P.2 hPr, ← annNorm_toAnn, map_sub, toAnn_coe, toAnn_coe]`. Establish `e2 : T.coeAnn (c (J + 1)) - T.coeAnn (c J) = (v - T.coeAnn (c J)) - (v - T.coeAnn (c (J + 1)))`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Conclude with `(T.annNorm_sub_le r _ _).trans_lt (max_lt (hcε J r) ((hcε (J + 1) r).trans_le (hεanti (Nat.le_succ J))))`. Rewrite `hsmall` using `[hcy (J + 1), map_mul, norm_mul, hvaly (J + 1) P hPr, ptProd, map_list_prod, List.map_map, List.norm_prod, List.map_map]`. Establish `hprod : ((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod < t J ^ (l (J + 1)).length`. Rewrite using `[hlen (J + 1), ← hεt J]`.

Establish `hq : 0 < Nr / R ^ m` using `div_pos hNr (pow_pos hR0 m)`. Rewrite using `[lt_div_iff₀ hNr]`. Use `(lt_div_iff₀ hq).2 hsmall` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.

Use `_ < ε J * R ^ m := by`. Use `mul_lt_mul_of_pos_right ?_ (pow_pos hR0 m)` and prove the remaining obligations. Simplify `hsmall` using `[Function.comp_def]`. Take `⟨Q, hQ, hQt⟩` from `exists_lt_of_prod_lt _ _ (fun Q => norm_nonneg _) (ht0 J).le hprod`. Conclude with `⟨Q, hQ, by rw [← T.ptEval_ξExt_eq_ptE P hPle]; exact hQt⟩`.

Establish `hne0 : (l 0) ≠ []`. Introduce `h`. Use `hlen 0` as an intermediate fact. Rewrite `this` using `[h, List.length_nil]`. Use linear arithmetic over natural numbers and integers.

Take `⟨P0, hP0⟩` from `List.exists_mem_of_ne_nil _ hne0`. Use `choose nextP hnextP hnextPt using hstep`. Set `chain : (J : ℕ) → {P : T.Pt // P ∈ l J}` to `fun J => Nat.rec ⟨P0, hP0⟩ (fun J P => ⟨nextP J P.1 P.2, hnextP J P.1 P.2⟩) J`. Establish `hchain : ∀ J, (chain (J + 1)).1 = nextP J (chain J).1 (chain J).2` using `fun J => rfl`. Use `set x : ℕ → T.Pt := fun J => (chain J).1`.

Establish `hxr : ∀ J, T.ptRad (x J).1 = R` using `fun J => hlrad J _ (chain J).2`. Establish `hxstep : ∀ J, ‖T.ptE (x J).2 ((x (J + 1)).1 : Γ)‖ < t J` using `fun J => by show ‖T.ptE (chain J).1.2 ((chain (J + 1)).1.1 : Γ)‖ < t J`. Rewrite using `[hchain]`. Conclude with `hnextPt J _ _`. Establish `hΓ : ∀ J, ∃ (q : T.int) (z : L) (V : Γ), IsUnit q ∧ ‖z‖ ≤ t J ∧ V ∈ T.int ∧ ((x (J + 1)).1 : Γ) = (x J).1 * q + T.teich z * V` using `fun J => T.exists_step_pt ((hxr (J + 1)).trans (hxr J).symm) (by rw [hxr J]; exact htR J) (hxstep J).le`.

Use `choose q z V hq hz hV hrel using hΓ`. Take `⟨η, hη, hηr, hηlim⟩` from `T.exists_limit_pt (fun J => (x J).1) (fun J => (x J).2) hxr q hq z V hV hrel t htanti htlim hz (by simp only [htdef]; nlinarith)`. Use `⟨η, hη, hηr, ?_⟩` and prove the remaining obligations. Establish `hηle : T.ptRad η ≤ ρ0` using `hηr.trans_le hr1.le`. Establish `hbound : ∀ J, ‖T.annEval hη (by rw [hηr]; exact r.2) v‖ ≤ max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m))`.

Introduce `J`. Establish `e : v = (v - T.coeAnn (c J)) + T.coeAnn (c J)` using `by ring`. Rewrite using `[e, map_add]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)` and prove the remaining obligations. Use `(T.norm_annEval_le hη _ _).trans ?_` and prove the remaining obligations.

Establish `: T.ptAnnRad (by rw [hηr]; exact r.2 : T.ptRad η ∈ Set.Icc (σ0 : ℝ) ρ0) = r` using `Subtype.ext hηr`. Rewrite using `[this]`. Conclude with `(hcε J r).le`. Rewrite using `[← toAnn_coe, annEval_toAnn, hcy J, map_mul, norm_mul]`. Establish `hperm` using `List.perm_cons_erase (chain J).2`.

Establish `hsplit : T.ptProd ρ0 (l J) = T.ξExt (x J).1 ρ0 * T.ptProd ρ0 ((l J).erase (x J))`. Rewrite using `[ptProd, (hperm.map _).prod_eq, List.map_cons, List.prod_cons]`. Both sides reduce to the same expression. Rewrite using `[hsplit, map_mul, norm_mul, T.ptEval_ξExt_eq_ptE ⟨η, hη⟩ hηle]`. Establish `h1 : ‖T.ptEval hη hηle (T.ptProd ρ0 ((l J).erase (x J)))‖ ≤ 1`.

Use `(T.norm_ptEval_le hη hηle _).trans ?_` and prove the remaining obligations. Rewrite using `[T.extNorm_ptProd _ _ fun P hP => by`. Rewrite using `[hlrad J P (List.mem_of_mem_erase hP)]`. Conclude with `hηr.ge]`. Conclude with `pow_le_one₀ (T.ptRad_pos' hη).le (T.ptRad_lt_one' hη).le`.

Establish `h2 : ‖T.ptEval hη hηle (y J)‖ ≤ Nr / R ^ m`. Use `(T.norm_ptEval_le hη hηle _).trans ?_` and prove the remaining obligations. Rewrite using `[hrIoc hη hηr, hny]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlim : Tendsto (fun J => max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m))) atTop (𝓝 0)`.

Use `hεlim.max (hηlim.mul_const (Nr / R ^ m))` as an intermediate fact. Rewrite `this` using `[zero_mul, max_self]`. Then use the resulting hypothesis. Conclude with `norm_eq_zero.1 (le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _))`.
-/
theorem exists_zero_ann (v : T.Ann ρ0 σ0) (hv : ∀ s, 0 < T.annNorm ρ0 σ0 s v) (r : AnnRad ρ0 σ0)
    (hr0 : (σ0 : ℝ) < r) (hr1 : (r : ℝ) < ρ0) (c0 : T.Econ ρ0)
    (hc0 : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c0) < T.annNorm ρ0 σ0 s v)
    (hm : 1 ≤ T.mult (c0 : T.RobbaExt ρ0) r) :
    ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ) (hrad : T.ptRad ξ = r),
      T.annEval hξ (by rw [hrad]; exact r.2) v = 0 := by
  classical
  set m : ℕ := (T.mult (c0 : T.RobbaExt ρ0) r).toNat with hmdef
  have hm' : (m : ℤ) = T.mult (c0 : T.RobbaExt ρ0) r := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  set R : ℝ := (r : ℝ) with hRdef
  have hR0 : 0 < R := σ0.2.1.trans hr0
  have hR1 : R < 1 := hr1.trans ρ0.2.2
  set Nr := T.annNorm ρ0 σ0 r v with hNrdef
  have hNr : 0 < Nr := hv r
  obtain ⟨μ, hμ, hμle⟩ := T.exists_pos_le_annNorm v hv

  set t : ℕ → ℝ := fun J => R ^ 2 / 2 * (1 / 2) ^ J with htdef
  have ht0 : ∀ J, 0 < t J := fun J => by simp only [htdef]; positivity
  have htR : ∀ J, t J < R := by
    intro J
    have h1 : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc t J ≤ R ^ 2 / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < R := by nlinarith
  have htanti : Antitone t := fun J K hJK => by
    simp only [htdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJK) (by positivity)
  have htlim : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (R ^ 2 / 2)
    rwa [mul_zero] at this
  set ε : ℕ → ℝ := fun J => Nr * (t J / R) ^ m with hεdef
  have hε0 : ∀ J, 0 < ε J := fun J => mul_pos hNr (pow_pos (div_pos (ht0 J) hR0) m)
  have hεanti : Antitone ε := fun J K hJK => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (ht0 K).le hR0.le) (div_le_div_of_nonneg_right (htanti hJK) hR0.le) m)
    hNr.le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun J => t J / R) atTop (𝓝 0) := by simpa using htlim.div_const R
    have h2 := (h1.pow m).const_mul Nr
    rwa [zero_pow (by omega), mul_zero] at h2
  have hεt : ∀ J, ε J * R ^ m / Nr = t J ^ m := fun J => by
    simp only [hεdef]; field_simp; rw [div_pow]; field_simp

  have happ : ∀ J, ∃ c : T.Econ ρ0, ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn c) < min (ε J) (μ / 2) :=
    fun J => T.exists_coeAnn_near v (lt_min (hε0 J) (half_pos hμ))
  choose c hc using happ
  have hgood : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < T.annNorm ρ0 σ0 s v := fun J s =>
    (hc J s).trans_le ((min_le_right _ _).trans ((half_le_self hμ.le).trans (hμle s)))
  have hcε : ∀ J s, T.annNorm ρ0 σ0 s (v - T.coeAnn (c J)) < ε J := fun J s =>
    (hc J s).trans_le (min_le_left _ _)
  have hc0' : ∀ J, (c J : T.RobbaExt ρ0) ≠ 0 := fun J =>
    T.coe_ne_zero_of_annNorm_sub_lt (annIn ρ0 σ0) (hgood J _)
  have hmJ : ∀ J, T.mult (c J : T.RobbaExt ρ0) R = m := fun J => by
    rw [hm']; exact (T.mult_eq_of_approx_ann hc0 (hgood J) hr0 hr1).symm

  have hfac : ∀ J, ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
      (∀ P ∈ l, R ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ R) ∧ (c J : T.RobbaExt ρ0) = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
        ∀ σ, R ≤ σ → σ ≤ R → T.mult y σ = 0 := fun J =>
    T.exists_factor_annulus T.rootExists hR0 le_rfl hr1 (hc0' J)
  choose l y hl hcy hy0 hym using hfac
  have hlrad : ∀ J, ∀ P ∈ l J, T.ptRad P.1 = R := fun J P hP => le_antisymm (hl J P hP).2 (hl J P hP).1
  have hlen : ∀ J, (l J).length = m := by
    intro J
    have h := hmJ J
    rw [hcy J, T.mult_mul (T.ptProd_ne_zero _) (hy0 J) ⟨hR0, hr1⟩, T.mult_ptProd _ ⟨hR0, hr1⟩ (hlrad J),
      hym J R le_rfl le_rfl, add_zero] at h
    exact_mod_cast h

  have hrIoc : ∀ {ξ : T.int} (hξ : T.IsPrimOne ξ) (hrad : T.ptRad ξ = R),
      T.ptRadIoc hξ (hrad.trans_le hr1.le) = annIoc r := fun hξ hrad => Subtype.ext hrad
  have hnc : ∀ J, T.extNorm ρ0 (annIoc r) (c J : T.RobbaExt ρ0) = Nr := by
    intro J
    rw [← annNorm_toAnn, toAnn_coe]
    exact T.annNorm_eq_of_sub_lt (hgood J r)
  have hny : ∀ J, T.extNorm ρ0 (annIoc r) (y J) = Nr / R ^ m := by
    intro J
    have h := hnc J
    rw [hcy J, extNorm_mul, T.extNorm_ptProd _ _ fun P hP => (hlrad J P hP).le, hlen J] at h
    have hRm : 0 < R ^ m := pow_pos hR0 m
    have hc : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = R := rfl
    rw [hc] at h
    rw [← h]; field_simp
  have hvaly : ∀ J (P : T.Pt) (hP : T.ptRad P.1 = R),
      ‖T.ptEval P.2 (hP.trans_le hr1.le) (y J)‖ = Nr / R ^ m := by
    intro J P hP
    have h := T.norm_ptEval_of_mult_eq_zero (hy0 J) P.2 (hP.trans_lt hr1)
      (by rw [hP]; exact hym J R le_rfl le_rfl)
    rw [h, hrIoc P.2 hP, hny]

  have hstep : ∀ J, ∀ P ∈ l J, ∃ Q ∈ l (J + 1), ‖T.ptE P.2 (Q.1 : Γ)‖ < t J := by
    intro J P hP
    have hPr := hlrad J P hP
    have hPle : T.ptRad P.1 ≤ ρ0 := hPr.trans_le hr1.le
    have h0 : T.ptEval P.2 hPle (c J : T.RobbaExt ρ0) = 0 := by
      rw [hcy J, map_mul, T.ptEval_ptProd_eq_zero_of_mem hP hPle, zero_mul]
    have hsmall : ‖T.ptEval P.2 hPle (c (J + 1) : T.RobbaExt ρ0)‖ < ε J := by
      have e : (c (J + 1) : T.RobbaExt ρ0) = ((c (J + 1) : T.RobbaExt ρ0) - c J) + c J := by ring
      rw [e, map_add, h0, add_zero]
      refine (T.norm_ptEval_le P.2 hPle _).trans_lt ?_
      rw [hrIoc P.2 hPr, ← annNorm_toAnn, map_sub, toAnn_coe, toAnn_coe]
      have e2 : T.coeAnn (c (J + 1)) - T.coeAnn (c J) = (v - T.coeAnn (c J)) - (v - T.coeAnn (c (J + 1))) := by
        ring
      rw [e2]
      exact (T.annNorm_sub_le r _ _).trans_lt (max_lt (hcε J r) ((hcε (J + 1) r).trans_le (hεanti (Nat.le_succ J))))
    rw [hcy (J + 1), map_mul, norm_mul, hvaly (J + 1) P hPr, ptProd, map_list_prod, List.map_map,
      List.norm_prod, List.map_map] at hsmall
    have hprod : ((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod < t J ^ (l (J + 1)).length := by
      rw [hlen (J + 1), ← hεt J]
      have hq : 0 < Nr / R ^ m := div_pos hNr (pow_pos hR0 m)
      rw [lt_div_iff₀ hNr]
      have := (lt_div_iff₀ hq).2 hsmall
      calc ((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod * Nr
          = (((l (J + 1)).map fun Q => ‖T.ptEval P.2 hPle (T.ξExt Q.1 ρ0)‖).prod * (Nr / R ^ m)) * R ^ m := by
            field_simp
        _ < ε J * R ^ m := by
            refine mul_lt_mul_of_pos_right ?_ (pow_pos hR0 m)
            simpa [Function.comp_def] using hsmall
    obtain ⟨Q, hQ, hQt⟩ := exists_lt_of_prod_lt _ _ (fun Q => norm_nonneg _) (ht0 J).le hprod
    exact ⟨Q, hQ, by rw [← T.ptEval_ξExt_eq_ptE P hPle]; exact hQt⟩

  have hne0 : (l 0) ≠ [] := by
    intro h; have := hlen 0; rw [h, List.length_nil] at this; omega
  obtain ⟨P0, hP0⟩ := List.exists_mem_of_ne_nil _ hne0
  choose nextP hnextP hnextPt using hstep
  let chain : (J : ℕ) → {P : T.Pt // P ∈ l J} := fun J =>
    Nat.rec ⟨P0, hP0⟩ (fun J P => ⟨nextP J P.1 P.2, hnextP J P.1 P.2⟩) J
  have hchain : ∀ J, (chain (J + 1)).1 = nextP J (chain J).1 (chain J).2 := fun J => rfl
  set x : ℕ → T.Pt := fun J => (chain J).1
  have hxr : ∀ J, T.ptRad (x J).1 = R := fun J => hlrad J _ (chain J).2
  have hxstep : ∀ J, ‖T.ptE (x J).2 ((x (J + 1)).1 : Γ)‖ < t J := fun J => by
    show ‖T.ptE (chain J).1.2 ((chain (J + 1)).1.1 : Γ)‖ < t J
    rw [hchain]; exact hnextPt J _ _
  have hΓ : ∀ J, ∃ (q : T.int) (z : L) (V : Γ), IsUnit q ∧ ‖z‖ ≤ t J ∧ V ∈ T.int ∧
      ((x (J + 1)).1 : Γ) = (x J).1 * q + T.teich z * V := fun J =>
    T.exists_step_pt ((hxr (J + 1)).trans (hxr J).symm) (by rw [hxr J]; exact htR J) (hxstep J).le
  choose q z V hq hz hV hrel using hΓ
  obtain ⟨η, hη, hηr, hηlim⟩ := T.exists_limit_pt (fun J => (x J).1) (fun J => (x J).2) hxr q hq z V hV hrel
    t htanti htlim hz (by simp only [htdef]; nlinarith)
  refine ⟨η, hη, hηr, ?_⟩

  have hηle : T.ptRad η ≤ ρ0 := hηr.trans_le hr1.le
  have hbound : ∀ J, ‖T.annEval hη (by rw [hηr]; exact r.2) v‖ ≤
      max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m)) := by
    intro J
    have e : v = (v - T.coeAnn (c J)) + T.coeAnn (c J) := by ring
    rw [e, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · refine (T.norm_annEval_le hη _ _).trans ?_
      have : T.ptAnnRad (by rw [hηr]; exact r.2 : T.ptRad η ∈ Set.Icc (σ0 : ℝ) ρ0) = r := Subtype.ext hηr
      rw [this]; exact (hcε J r).le
    · rw [← toAnn_coe, annEval_toAnn, hcy J, map_mul, norm_mul]
      have hperm := List.perm_cons_erase (chain J).2
      have hsplit : T.ptProd ρ0 (l J) = T.ξExt (x J).1 ρ0 * T.ptProd ρ0 ((l J).erase (x J)) := by
        rw [ptProd, (hperm.map _).prod_eq, List.map_cons, List.prod_cons]; rfl
      rw [hsplit, map_mul, norm_mul, T.ptEval_ξExt_eq_ptE ⟨η, hη⟩ hηle]
      have h1 : ‖T.ptEval hη hηle (T.ptProd ρ0 ((l J).erase (x J)))‖ ≤ 1 := by
        refine (T.norm_ptEval_le hη hηle _).trans ?_
        rw [T.extNorm_ptProd _ _ fun P hP => by
          rw [hlrad J P (List.mem_of_mem_erase hP)]; exact hηr.ge]
        exact pow_le_one₀ (T.ptRad_pos' hη).le (T.ptRad_lt_one' hη).le
      have h2 : ‖T.ptEval hη hηle (y J)‖ ≤ Nr / R ^ m := by
        refine (T.norm_ptEval_le hη hηle _).trans ?_
        rw [hrIoc hη hηr, hny]
      calc ‖T.ptE hη ((x J).1 : Γ)‖ * ‖T.ptEval hη hηle (T.ptProd ρ0 ((l J).erase (x J)))‖ *
            ‖T.ptEval hη hηle (y J)‖ ≤ ‖T.ptE hη ((x J).1 : Γ)‖ * 1 * (Nr / R ^ m) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ = ‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m) := by ring
  have hlim : Tendsto (fun J => max (ε J) (‖T.ptE hη ((x J).1 : Γ)‖ * (Nr / R ^ m))) atTop (𝓝 0) := by
    have := hεlim.max (hηlim.mul_const (Nr / R ^ m))
    rwa [zero_mul, max_self] at this
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _))

end TeichLift

end GroundTheory.PAdicHodge
