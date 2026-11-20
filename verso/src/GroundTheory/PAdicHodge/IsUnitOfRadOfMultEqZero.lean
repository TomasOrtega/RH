import Mathlib
import GroundTheory.PAdicHodge.ExistsIsRootForallNormPowMulLe
import GroundTheory.PAdicHodge.ExtRobbaPointDiv
import GroundTheory.PAdicHodge.ExtRobbaUnits
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

/- English proof (translation)
Simplify using `[lowIdx]`.
-/
theorem lowIdx_zero {ρ0 : Set.Ioo (0 : ℝ) 1} (σ : ℝ) : T.lowIdx (0 : T.RobbaExt ρ0) σ = 0 := by
  simp [lowIdx]

/- English proof (translation)
Simplify using `[highIdx]`.
-/
theorem highIdx_zero {ρ0 : Set.Ioo (0 : ℝ) 1} (σ : ℝ) : T.highIdx (0 : T.RobbaExt ρ0) σ = 0 := by
  simp [highIdx]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[map_zero, lowIdx_zero, lowIdx_zero, highIdx_zero, highIdx_zero]`. Conclude with `⟨rfl, rfl⟩`. Establish `hxr : T.res h x ≠ 0` using `fun h0 => hx (T.res_injective h (h0.trans (map_zero _).symm))`.

Use `set η := ((ρ1 : ℝ) - σ) / 2 with hηdef`. Establish `hη : 0 < η` using `by rw [hηdef]; linarith [hσ.2]`. Establish `hη1 : σ + η ≤ ρ1` using `by rw [hηdef]; linarith [hσ.2]`. Establish `hη0 : σ + η ≤ ρ0` using `hη1.trans h`. Take `⟨c, hc⟩` from `T.exists_approx_norm hx ⟨σ, hσ.1, (hσ.2.le.trans h)⟩ ⟨σ + η, by linarith [hσ.1], hη0⟩ (show σ ≤ σ + η by linarith)`.

Establish `h1` using `T.idx_eq_of_approx hx ⟨hσ.1, hσ.2.trans_le h⟩ hη hη0 hc`. Establish `hc' : ∀ τ : Set.Ioc (0 : ℝ) ρ1, σ ≤ τ → (τ : ℝ) ≤ σ + η → T.extNorm ρ1 τ (T.res h x - ((T.incl h c : T.Econ ρ1) : T.RobbaExt ρ1)) < T.extNorm ρ1 τ (T.res h x)`. Introduce `τ h1' h2'`. Rewrite using `[← T.res_coe h c, ← map_sub, T.extNorm_res, T.extNorm_res]`. Conclude with `hc ⟨τ, τ.2.1, τ.2.2.trans h⟩ h1' h2'`.

Establish `h2` using `T.idx_eq_of_approx hxr hσ hη hη1 hc'`. Rewrite using `[h2.1, h2.2, h1.1, h1.2]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem idx_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) {σ : ℝ}
    (hσ : 0 < σ ∧ σ < ρ1) :
    T.lowIdx (T.res h x) σ = T.lowIdx x σ ∧ T.highIdx (T.res h x) σ = T.highIdx x σ := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, lowIdx_zero, lowIdx_zero, highIdx_zero, highIdx_zero]; exact ⟨rfl, rfl⟩
  have hxr : T.res h x ≠ 0 := fun h0 => hx (T.res_injective h (h0.trans (map_zero _).symm))
  set η := ((ρ1 : ℝ) - σ) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith [hσ.2]
  have hη1 : σ + η ≤ ρ1 := by rw [hηdef]; linarith [hσ.2]
  have hη0 : σ + η ≤ ρ0 := hη1.trans h
  obtain ⟨c, hc⟩ := T.exists_approx_norm hx ⟨σ, hσ.1, (hσ.2.le.trans h)⟩
    ⟨σ + η, by linarith [hσ.1], hη0⟩ (show σ ≤ σ + η by linarith)
  have h1 := T.idx_eq_of_approx hx ⟨hσ.1, hσ.2.trans_le h⟩ hη hη0 hc
  have hc' : ∀ τ : Set.Ioc (0 : ℝ) ρ1, σ ≤ τ → (τ : ℝ) ≤ σ + η →
      T.extNorm ρ1 τ (T.res h x - ((T.incl h c : T.Econ ρ1) : T.RobbaExt ρ1)) <
        T.extNorm ρ1 τ (T.res h x) := by
    intro τ h1' h2'
    rw [← T.res_coe h c, ← map_sub, T.extNorm_res, T.extNorm_res]
    exact hc ⟨τ, τ.2.1, τ.2.2.trans h⟩ h1' h2'
  have h2 := T.idx_eq_of_approx hxr hσ hη hη1 hc'
  rw [h2.1, h2.2, h1.1, h1.2]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `T.idx_res h x hσ`. Rewrite using `[mult, mult, h1, h2]`.
-/
theorem mult_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) {σ : ℝ}
    (hσ : 0 < σ ∧ σ < ρ1) : T.mult (T.res h x) σ = T.mult x σ := by
  obtain ⟨h1, h2⟩ := T.idx_res h x hσ
  rw [mult, mult, h1, h2]

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)

/- English proof (translation)
The claim follows from `Completion.induction_on x (isClosed_eq ((T.continuous_ptEval hξ hr1).comp (T.continuous_res h)) (T.continuous_ptEval hξ _)) fun b => by rw [T.res_coe, ptEval_coe, ptEval_coe]; rfl`.
-/
theorem ptEval_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (hr1 : T.ptRad ξ ≤ ρ1)
    (x : T.RobbaExt ρ0) :
    T.ptEval hξ hr1 (T.res h x) = T.ptEval hξ (hr1.trans h) x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_ptEval hξ hr1).comp (T.continuous_res h))
      (T.continuous_ptEval hξ _))
    fun b => by rw [T.res_coe, ptEval_coe, ptEval_coe]; rfl

/- English proof (translation)
Rewrite using `[ξExt, T.res_coe]`. Both sides reduce to the same expression.
-/
theorem res_ξExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    T.res h (T.ξExt ξ ρ0) = T.ξExt ξ ρ1 := by
  rw [ξExt, T.res_coe]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨huniq _ (lowIndex_mem hρ hc ha), huniq _ (highIndex_mem hρ hc ha)⟩`.
-/
theorem idx_eq_of_domSet_singleton {a : ℤ → L} {ρ : ℝ} (hρ : 0 < ρ) (hc : ConvergesAt a ρ)
    (ha : a ≠ 0) {k : ℤ} (hk : k ∈ domSet a ρ) (huniq : ∀ n ∈ domSet a ρ, n = k) :
    lowIndex a ρ = k ∧ highIndex a ρ = k :=
  ⟨huniq _ (lowIndex_mem hρ hc ha), huniq _ (highIndex_mem hρ hc ha)⟩

include hξ in
/- English proof (translation)
Use `set r := T.ptRad ξ with hrdef`. Establish `hr0 : 0 < r` using `T.ptRad_pos' hξ`. Establish `hc` using `T.convergesAt_of_mem_int ξ.2 hσ0 hσ1`. Establish `hne : T.zcoeff (ξ : Γ) ≠ 0`. Introduce `h`.

Use `congrFun h 0` as an intermediate fact. Rewrite `this` using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]`. Conclude with `hξ.coeff_zero_ne this`. Establish `hg : gaussNorm (T.zcoeff (ξ : Γ)) σ = max r σ` using `T.gaussNorm_prim hξ hσ0 hσ1`. Establish `w0 : ‖T.zcoeff (ξ : Γ) 0‖ * σ ^ (0 : ℤ) = r`.

Rewrite using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]`. Simplify using `[hrdef, ptRad]`. Establish `w1 : ‖T.zcoeff (ξ : Γ) 1‖ * σ ^ (1 : ℤ) = σ`. Rewrite using `[show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul, Nat.cast_one, zpow_one]`. Establish `wlarge : ∀ n : ℤ, 2 ≤ n → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n < σ`.

Introduce `n hn`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)`. Rewrite using `[T.zcoeff_natCast, zpow_natCast]`. Establish `hk : 2 ≤ k` using `by omega`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `wneg : ∀ n : ℤ, n < 0 → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = 0` using `fun n hn => by`. Rewrite using `[T.zcoeff_of_neg _ hn, norm_zero, zero_mul]`. Establish `hdom : ∀ n, n ∈ domSet (T.zcoeff (ξ : Γ)) σ ↔ ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = max r σ` using `fun n => by`.

Simplify using `only [domSet, Set.mem_setOf_eq, hg]`. Break down `lt_trichotomy σ r with hlt | heq | hgt` into its components or cases. Establish `h0 : (0 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ`. Rewrite using `[hdom, w0, max_eq_left hlt.le]`. Establish `hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 0`.

Introduce `n hn`. Rewrite `hn` using `[hdom, max_eq_left hlt.le]`. Assume the negation of the conclusion as `hn0`. Break down `lt_or_gt_of_ne hn0 with hneg | hpos` into its components or cases. Rewrite `hn` using `[wneg n hneg]`.

Combine the linear equalities and inequalities to obtain the conclusion. Break down `(show n = 1 ∨ 2 ≤ n by omega) with rfl | h2` into its components or cases. Rewrite `hn` using `[w1]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `wlarge n h2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `idx_eq_of_domSet_singleton hσ0 hc hne h0 hu` as an intermediate fact. Rewrite using `[if_pos hlt.le, if_pos hlt]`. Conclude with `this`. Establish `hs` using `T.idx_prim_self hξ`.

Substitute `heq` using the available equality. Rewrite using `[if_pos le_rfl, if_neg (lt_irrefl _)]`. Conclude with `hs`. Establish `h1 : (1 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ`. Rewrite using `[hdom, w1, max_eq_right hgt.le]`.

Establish `hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 1`. Introduce `n hn`. Rewrite `hn` using `[hdom, max_eq_right hgt.le]`. Assume the negation of the conclusion as `hn1`. Break down `(show n < 0 ∨ n = 0 ∨ 2 ≤ n by omega) with hneg | rfl | h2` into its components or cases.

Rewrite `hn` using `[wneg n hneg]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hn` using `[w0]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `wlarge n h2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `idx_eq_of_domSet_singleton hσ0 hc hne h1 hu` as an intermediate fact. Rewrite using `[if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le)]`. Conclude with `this`.
-/
theorem idx_zcoeff_prim {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    lowIndex (T.zcoeff (ξ : Γ)) σ = (if σ ≤ T.ptRad ξ then 0 else 1) ∧
      highIndex (T.zcoeff (ξ : Γ)) σ = (if σ < T.ptRad ξ then 0 else 1) := by
  set r := T.ptRad ξ with hrdef
  have hr0 : 0 < r := T.ptRad_pos' hξ
  have hc := T.convergesAt_of_mem_int ξ.2 hσ0 hσ1
  have hne : T.zcoeff (ξ : Γ) ≠ 0 := by
    intro h; have := congrFun h 0; rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast] at this
    exact hξ.coeff_zero_ne this
  have hg : gaussNorm (T.zcoeff (ξ : Γ)) σ = max r σ := T.gaussNorm_prim hξ hσ0 hσ1
  have w0 : ‖T.zcoeff (ξ : Γ) 0‖ * σ ^ (0 : ℤ) = r := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]; simp [hrdef, ptRad]
  have w1 : ‖T.zcoeff (ξ : Γ) 1‖ * σ ^ (1 : ℤ) = σ := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul,
      Nat.cast_one, zpow_one]
  have wlarge : ∀ n : ℤ, 2 ≤ n → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n < σ := by
    intro n hn
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
    rw [T.zcoeff_natCast, zpow_natCast]
    have hk : 2 ≤ k := by omega
    calc ‖T.coeff (ξ : Γ) k‖ * σ ^ k ≤ 1 * σ ^ k :=
          mul_le_mul_of_nonneg_right (T.norm_coeff_prim_le hξ k) (by positivity)
      _ < σ := by
          rw [one_mul]
          calc σ ^ k ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσ1.le hk
            _ < σ := by nlinarith
  have wneg : ∀ n : ℤ, n < 0 → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = 0 := fun n hn => by
    rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]
  have hdom : ∀ n, n ∈ domSet (T.zcoeff (ξ : Γ)) σ ↔
      ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = max r σ := fun n => by
    simp only [domSet, Set.mem_setOf_eq, hg]
  rcases lt_trichotomy σ r with hlt | heq | hgt
  · have h0 : (0 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ := by
      rw [hdom, w0, max_eq_left hlt.le]
    have hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 0 := by
      intro n hn
      rw [hdom, max_eq_left hlt.le] at hn
      by_contra hn0
      rcases lt_or_gt_of_ne hn0 with hneg | hpos
      · rw [wneg n hneg] at hn; linarith
      · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
        · rw [w1] at hn; linarith
        · have := wlarge n h2; linarith
    have := idx_eq_of_domSet_singleton hσ0 hc hne h0 hu
    rw [if_pos hlt.le, if_pos hlt]
    exact this
  · have hs := T.idx_prim_self hξ
    subst heq
    rw [if_pos le_rfl, if_neg (lt_irrefl _)]
    exact hs
  · have h1 : (1 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ := by
      rw [hdom, w1, max_eq_right hgt.le]
    have hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 1 := by
      intro n hn
      rw [hdom, max_eq_right hgt.le] at hn
      by_contra hn1
      rcases (show n < 0 ∨ n = 0 ∨ 2 ≤ n by omega) with hneg | rfl | h2
      · rw [wneg n hneg] at hn; linarith
      · rw [w0] at hn; linarith
      · have := wlarge n h2; linarith
    have := idx_eq_of_domSet_singleton hσ0 hc hne h1 hu
    rw [if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le)]
    exact this

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

include hξ in
/- English proof (translation)
Introduce `h`. Use `T.ptRad_le_extNorm_ξExt (ξ := ξ) (ρ0 := ρ0) (topRad ρ0)` as an intermediate fact. Rewrite `this` using `[h, extNorm_zero]`. Conclude with `absurd this (not_le.2 (T.ptRad_pos' hξ))`.
-/
theorem ptExt_ne_zero : T.ξExt ξ ρ0 ≠ 0 := by
  intro h
  have := T.ptRad_le_extNorm_ξExt (ξ := ξ) (ρ0 := ρ0) (topRad ρ0)
  rw [h, extNorm_zero] at this
  exact absurd this (not_le.2 (T.ptRad_pos' hξ))

include hξ in
/- English proof (translation)
Establish `h` using `T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩) (T.ptExt_ne_zero hξ) hσ`. Rewrite `h` using `[show ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0) = T.ξExt ξ ρ0 from rfl]`. Rewrite using `[h.1, h.2]`. Use `show lowIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _ ∧ highIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _`. Rewrite using `[coeffB_algebraMap]`.

Conclude with `T.idx_zcoeff_prim hξ hσ.1 (hσ.2.trans ρ0.2.2)`.
-/
theorem idx_ptExt {σ : ℝ} (hσ : 0 < σ ∧ σ < ρ0) :
    T.lowIdx (T.ξExt ξ ρ0) σ = (if σ ≤ T.ptRad ξ then 0 else 1) ∧
      T.highIdx (T.ξExt ξ ρ0) σ = (if σ < T.ptRad ξ then 0 else 1) := by
  have h := T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩)
    (T.ptExt_ne_zero hξ) hσ
  rw [show ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0) = T.ξExt ξ ρ0 from rfl] at h
  rw [h.1, h.2]
  show lowIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _ ∧ highIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _
  rw [coeffB_algebraMap]
  exact T.idx_zcoeff_prim hξ hσ.1 (hσ.2.trans ρ0.2.2)

include hξ in
/- English proof (translation)
Take `⟨h1, h2⟩` from `T.idx_ptExt hξ hσ`. Rewrite using `[mult, h1, h2]`. Break down `lt_trichotomy σ (T.ptRad ξ) with hlt | heq | hgt` into its components or cases. Rewrite using `[if_pos hlt.le, if_pos hlt, if_neg hlt.ne]`. Both sides reduce to the same expression.

Rewrite using `[if_pos heq.le, if_neg (lt_irrefl _ ∘ (heq ▸ ·)), if_pos heq]`. Both sides reduce to the same expression. Rewrite using `[if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le), if_neg hgt.ne']`. Both sides reduce to the same expression.
-/
theorem mult_ptExt {σ : ℝ} (hσ : 0 < σ ∧ σ < ρ0) :
    T.mult (T.ξExt ξ ρ0) σ = if σ = T.ptRad ξ then 1 else 0 := by
  obtain ⟨h1, h2⟩ := T.idx_ptExt hξ hσ
  rw [mult, h1, h2]
  rcases lt_trichotomy σ (T.ptRad ξ) with hlt | heq | hgt
  · rw [if_pos hlt.le, if_pos hlt, if_neg hlt.ne]; rfl
  · rw [if_pos heq.le, if_neg (lt_irrefl _ ∘ (heq ▸ ·)), if_pos heq]; rfl
  · rw [if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le), if_neg hgt.ne']; rfl

def vInv : T.int := ↑((T.isUnit_ξtail hξ).unit⁻¹)

/- English proof (translation)
Use `(T.isUnit_ξtail hξ).mul_val_inv` as an intermediate fact. Conclude with `congrArg Subtype.val this`.
-/
theorem ξtail_mul_vInv : (T.ξtail ξ : Γ) * (T.vInv hξ : Γ) = 1 := by
  have := (T.isUnit_ξtail hξ).mul_val_inv
  exact congrArg Subtype.val this

/- English proof (translation)
Establish `h1` using `congrArg T.red (T.ξtail_mul_vInv hξ)`. Rewrite `h1` using `[map_mul, map_one]`. Establish `hV` using `T.norm_red_le_one _ (T.ξtail ξ).2`. Establish `hW` using `T.norm_red_le_one _ (T.vInv hξ).2`. Establish `hprod` using `congrArg norm h1`.

Rewrite `hprod` using `[norm_mul, norm_one]`. Use `le_antisymm hW ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg (T.red (T.ξtail ξ : Γ)), norm_nonneg (T.red (T.vInv hξ : Γ))]`.
-/
theorem norm_red_vInv : ‖T.red (T.vInv hξ : Γ)‖ = 1 := by
  have h1 := congrArg T.red (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at h1
  have hV := T.norm_red_le_one _ (T.ξtail ξ).2
  have hW := T.norm_red_le_one _ (T.vInv hξ).2
  have hprod := congrArg norm h1
  rw [norm_mul, norm_one] at hprod
  refine le_antisymm hW ?_
  nlinarith [norm_nonneg (T.red (T.ξtail ξ : Γ)), norm_nonneg (T.red (T.vInv hξ : Γ))]

def normU : Γ := T.teich (T.coeff (ξ : Γ) 0) * (T.vInv hξ : Γ)

/- English proof (translation)
The claim follows from `T.int.mul_mem (T.teich_mem_int (T.norm_coeff_prim_le hξ 0)) (T.vInv hξ).2`.
-/
theorem normU_mem_int : T.normU hξ ∈ T.int :=
  T.int.mul_mem (T.teich_mem_int (T.norm_coeff_prim_le hξ 0)) (T.vInv hξ).2

/- English proof (translation)
Rewrite using `[normU, T.gaussNorm_zcoeff_mul hρ0 hρ1 (T.convergesAt_teich _ ρ) (T.convergesAt_of_mem_int (T.vInv hξ).2 hρ0 hρ1), T.gaussNorm_teich _ hρ0, T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, mul_one]`. Both sides reduce to the same expression.
-/
theorem gaussNorm_normU {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    gaussNorm (T.zcoeff (T.normU hξ)) ρ = T.ptRad ξ := by
  rw [normU, T.gaussNorm_zcoeff_mul hρ0 hρ1 (T.convergesAt_teich _ ρ)
    (T.convergesAt_of_mem_int (T.vInv hξ).2 hρ0 hρ1), T.gaussNorm_teich _ hρ0,
    T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, mul_one]
  rfl

def normPt : T.B := 1 + algebraMap Γ T.B (T.normU hξ) * IsLocalization.Away.invSelf T.π

/- English proof (translation)
Establish `hξe` using `T.coe_eq_teich_add ξ`. Establish `hinv` using `IsLocalization.Away.mul_invSelf (S := T.B) T.π`. Establish `hV` using `congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)`. Rewrite `hV` using `[map_mul, map_one]`. Rewrite using `[normPt, normU]`.

Generalize the expression as in `T.coeff (ξ : Γ) 0 = c0 at hξe ⊢`. Rewrite using `[hξe]`. Simplify using `only [map_add, map_mul]`. Take the linear combination `(-(algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) * hinv - hV)`.
-/
theorem normPt_eq : T.normPt hξ =
    algebraMap Γ T.B ξ * algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π := by
  have hξe := T.coe_eq_teich_add ξ
  have hinv := IsLocalization.Away.mul_invSelf (S := T.B) T.π
  have hV := congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at hV
  rw [normPt, normU]
  generalize T.coeff (ξ : Γ) 0 = c0 at hξe ⊢
  rw [hξe]
  simp only [map_add, map_mul]
  linear_combination (-(algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) *
    hinv - hV)

/- English proof (translation)
Rewrite using `[mem_Econ, coeffB_algebraMap]`. Conclude with `T.convergesAt_of_mem_int hx ρ.2.1 ρ.2.2`.
-/
theorem algebraMap_int_mem_Econ {x : Γ} (hx : x ∈ T.int) (ρ : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B x ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_of_mem_int hx ρ.2.1 ρ.2.2

/- English proof (translation)
The claim follows from `(T.Econ ρ).add_mem (T.Econ ρ).one_mem ((T.Econ ρ).mul_mem (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ρ) (T.invSelf_mem_Econ ρ))`.
-/
theorem normPt_mem_Econ (ρ : Set.Ioo (0 : ℝ) 1) : T.normPt hξ ∈ T.Econ ρ :=
  (T.Econ ρ).add_mem (T.Econ ρ).one_mem
    ((T.Econ ρ).mul_mem (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ρ) (T.invSelf_mem_Econ ρ))

def normPtExt (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨T.normPt hξ, T.normPt_mem_Econ hξ ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)

def normUnit (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π,
    (T.Econ ρ0).mul_mem (T.algebraMap_int_mem_Econ (T.vInv hξ).2 ρ0) (T.invSelf_mem_Econ ρ0)⟩ :
      T.Econ ρ0) : T.RobbaExt ρ0)

def normUnitInv (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.ξtail ξ) * algebraMap Γ T.B T.π,
    (T.Econ ρ0).mul_mem (T.algebraMap_int_mem_Econ (T.ξtail ξ).2 ρ0) (T.algebraMap_π_mem_Econ ρ0)⟩ :
      T.Econ ρ0) : T.RobbaExt ρ0)

/- English proof (translation)
Rewrite using `[normUnit, normUnitInv, ← Completion.coe_mul, ← Completion.coe_one]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hinv` using `IsLocalization.Away.mul_invSelf (S := T.B) T.π`. Establish `hV` using `congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)`.

Rewrite `hV` using `[map_mul, map_one]`. Use `show algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π * (algebraMap Γ T.B (T.ξtail ξ) * algebraMap Γ T.B T.π) = 1`. Take the linear combination `(algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) * hinv + hV`.
-/
theorem normUnit_mul_inv (ρ0 : Set.Ioo (0 : ℝ) 1) : T.normUnit hξ ρ0 * T.normUnitInv (ξ := ξ) ρ0 = 1 := by
  rw [normUnit, normUnitInv, ← Completion.coe_mul, ← Completion.coe_one]
  congr 1
  apply Subtype.ext
  have hinv := IsLocalization.Away.mul_invSelf (S := T.B) T.π
  have hV := congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at hV
  show algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π *
    (algebraMap Γ T.B (T.ξtail ξ) * algebraMap Γ T.B T.π) = 1
  linear_combination (algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) * hinv +
    hV

/- English proof (translation)
Rewrite using `[normPtExt, ξExt, normUnit, ← Completion.coe_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show T.normPt hξ = algebraMap Γ T.B ξ * (algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π)`. Rewrite using `[normPt_eq, mul_assoc]`.
-/
theorem normPtExt_eq (ρ0 : Set.Ioo (0 : ℝ) 1) :
    T.normPtExt hξ ρ0 = T.ξExt ξ ρ0 * T.normUnit hξ ρ0 := by
  rw [normPtExt, ξExt, normUnit, ← Completion.coe_mul]
  congr 1
  apply Subtype.ext
  show T.normPt hξ = algebraMap Γ T.B ξ * (algebraMap Γ T.B (T.vInv hξ) *
    IsLocalization.Away.invSelf T.π)
  rw [normPt_eq, mul_assoc]

/- English proof (translation)
Rewrite using `[normPtExt_eq, mul_assoc, normUnit_mul_inv, mul_one]`.
-/
theorem ξExt_eq_normPtExt (ρ0 : Set.Ioo (0 : ℝ) 1) :
    T.ξExt ξ ρ0 = T.normPtExt hξ ρ0 * T.normUnitInv (ξ := ξ) ρ0 := by
  rw [normPtExt_eq, mul_assoc, normUnit_mul_inv, mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨T.normUnitInv (ξ := ξ) ρ0 * y, by rw [ξExt_eq_normPtExt, mul_assoc]⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨T.normUnit hξ ρ0 * y, by rw [normPtExt_eq, mul_assoc]⟩`.
-/
theorem dvd_ξExt_iff_normPtExt {ρ0 : Set.Ioo (0 : ℝ) 1} (x : T.RobbaExt ρ0) :
    T.ξExt ξ ρ0 ∣ x ↔ T.normPtExt hξ ρ0 ∣ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨T.normUnitInv (ξ := ξ) ρ0 * y, by rw [ξExt_eq_normPtExt, mul_assoc]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨T.normUnit hξ ρ0 * y, by rw [normPtExt_eq, mul_assoc]⟩

/- English proof (translation)
Rewrite using `[normPtExt, ← Completion.coe_one, ← Completion.coe_sub, extNorm_coe]`. Use `show gaussNorm (T.coeffB (T.normPt hξ - 1)) ρ = _`. Rewrite using `[normPt, add_sub_cancel_left]`. Establish `hρ0` using `rad_pos ρ0 ρ`. Establish `hρ1` using `rad_lt_one ρ0 ρ`.

Rewrite using `[(T.convergesAt_coeffB_mul hρ0 hρ1 (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ⟨ρ, hρ0, hρ1⟩) (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap, T.gaussNorm_normU hξ hρ0 hρ1, coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_neg, zpow_one, div_eq_mul …`.
-/
theorem extNorm_normPtExt_sub_one {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normPtExt hξ ρ0 - 1) = T.ptRad ξ / ρ := by
  rw [normPtExt, ← Completion.coe_one, ← Completion.coe_sub, extNorm_coe]
  show gaussNorm (T.coeffB (T.normPt hξ - 1)) ρ = _
  rw [normPt, add_sub_cancel_left]
  have hρ0 := rad_pos ρ0 ρ
  have hρ1 := rad_lt_one ρ0 ρ
  rw [(T.convergesAt_coeffB_mul hρ0 hρ1
    (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ⟨ρ, hρ0, hρ1⟩)
    (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap, T.gaussNorm_normU hξ hρ0 hρ1,
    coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_neg, zpow_one, div_eq_mul_inv]

include hξ in
/- English proof (translation)
Rewrite using `[ξExt, extNorm_coe]`. Use `show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) ρ = _`. Rewrite using `[coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ)]`. Both sides reduce to the same expression.
-/
theorem extNorm_ptExt {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.ξExt ξ ρ0) = max (T.ptRad ξ) ρ := by
  rw [ξExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) ρ = _
  rw [coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ)]
  rfl

/- English proof (translation)
Rewrite using `[normUnit, extNorm_coe]`. Establish `hρ0` using `rad_pos ρ0 ρ`. Establish `hρ1` using `rad_lt_one ρ0 ρ`. Use `show gaussNorm (T.coeffB (algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π)) ρ = _`. Rewrite using `[(T.convergesAt_coeffB_mul hρ0 hρ1 (T.algebraMap_int_mem_Econ (T.vInv hξ).2 ⟨ρ, hρ0, hρ1⟩) (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap, T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, one_mul, coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, nor …`.
-/
theorem extNorm_normUnit {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normUnit hξ ρ0) = (ρ : ℝ)⁻¹ := by
  rw [normUnit, extNorm_coe]
  have hρ0 := rad_pos ρ0 ρ
  have hρ1 := rad_lt_one ρ0 ρ
  show gaussNorm (T.coeffB (algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π)) ρ = _
  rw [(T.convergesAt_coeffB_mul hρ0 hρ1
    (T.algebraMap_int_mem_Econ (T.vInv hξ).2 ⟨ρ, hρ0, hρ1⟩)
    (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap,
    T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, one_mul,
    coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_neg, zpow_one]

/- English proof (translation)
Rewrite using `[normPtExt_eq, extNorm_mul, T.extNorm_ptExt hξ, T.extNorm_normUnit hξ]`. Establish `hρ0` using `rad_pos ρ0 ρ`. Rewrite using `[← div_eq_mul_inv, ← max_div_div_right hρ0.le, div_self hρ0.ne', max_comm]`.
-/
theorem extNorm_normPtExt {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normPtExt hξ ρ0) = max 1 (T.ptRad ξ / ρ) := by
  rw [normPtExt_eq, extNorm_mul, T.extNorm_ptExt hξ, T.extNorm_normUnit hξ]
  have hρ0 := rad_pos ρ0 ρ
  rw [← div_eq_mul_inv, ← max_div_div_right hρ0.le, div_self hρ0.ne', max_comm]

/- English proof (translation)
Establish `hs` using `T.sum_mult_breaksR hx hρ hρρ1 hρ1`. Establish `h0 : ∑ σ ∈ (T.breaksR_finite hx hρ hρρ1 hρ1).toFinset, T.mult x σ = 0` using `Finset.sum_eq_zero fun σ hσ => by`. Simplify using `only [Set.Finite.mem_toFinset, breaksR, Set.mem_setOf_eq] at hσ`. Conclude with `h σ (hρ.trans_le hσ.1.1) (hσ.1.2.trans_lt hρ1)`. Establish `hm1` using `h ρ1 (hρ.trans_le hρρ1) hρ1`.

Rewrite `hm1` using `[mult]`. Rewrite `hs` using `[h0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lowIdx_const_of_mult_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) {ρ ρ1 : ℝ} (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1)
    (hρ1 : ρ1 < ρ0) : T.lowIdx x ρ = T.lowIdx x ρ1 := by
  have hs := T.sum_mult_breaksR hx hρ hρρ1 hρ1
  have h0 : ∑ σ ∈ (T.breaksR_finite hx hρ hρρ1 hρ1).toFinset, T.mult x σ = 0 :=
    Finset.sum_eq_zero fun σ hσ => by
      simp only [Set.Finite.mem_toFinset, breaksR, Set.mem_setOf_eq] at hσ
      exact h σ (hρ.trans_le hσ.1.1) (hσ.1.2.trans_lt hρ1)
  have hm1 := h ρ1 (hρ.trans_le hρρ1) hρ1
  rw [mult] at hm1
  rw [h0] at hs
  omega

/- English proof (translation)
Use `set ρ2 := (ρ1 + (ρ0 : ℝ)) / 2 with hρ2`. Establish `hρ2a : ρ1 < ρ2` using `by rw [hρ2]; linarith`. Establish `hρ2b : ρ2 ≤ ρ0` using `by rw [hρ2]; linarith`. Establish `hρ1pos : 0 < ρ1` using `hρ.trans_le hρρ1`. Take `⟨c, hc⟩` from `T.exists_approx_norm hx ⟨ρ, hρ, (hρρ1.trans hρ1.le)⟩ ⟨ρ2, by linarith, hρ2b⟩ (show ρ ≤ ρ2 by linarith)`.

Establish `key : ∀ σ : ℝ, ρ ≤ σ → σ ≤ ρ1 → T.normR x σ = ‖T.coeffB c (T.lowIdx x σ)‖ * σ ^ T.lowIdx x σ`. Introduce `σ h1 h2`. Establish `hσ0 : 0 < σ` using `hρ.trans_le h1`. Use `set s : Set.Ioc (0 : ℝ) ρ0 := ⟨σ, hσ0, (h2.trans hρ1.le)⟩`. Establish `hcs` using `hc s h1 (by show σ ≤ ρ2; linarith)`.

Establish `hidx` using `T.idx_eq_of_approx hx ⟨hσ0, h2.trans_lt hρ1⟩ (η := ρ2 - σ) (by linarith) (by linarith) fun τ hτ1 hτ2 => hc τ (h1.trans hτ1) (by linarith)`. Establish `hc0 : T.coeffB c ≠ 0`. Introduce `h0`. Use `T.coe_ne_zero_of_approx hcs` as an intermediate fact. Take `⟨N, y, hy⟩` from `IsLocalization.Away.surj T.π (c : T.B)`.

Establish `hy0 : y ≠ 0` using `by rintro rfl; exact this (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))`. Rewrite `h0` using `[T.coeffB_eq hy]`. Apply `hy0` to reduce the goal to its premises. Use `(T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)` and prove the remaining obligations. Use `congrFun h0 (k - N)` as an intermediate fact.

Simplify using `using this`. Rewrite using `[T.normR_eq x s, ← T.extNorm_eq_of_lt hcs, extNorm_coe, hidx.1]`. Conclude with `(lowIndex_mem hσ0 (T.convergesAt_rad ρ0 c s) hc0).symm`. Establish `hconst` using `T.lowIdx_const_of_mult_zero hx h hρ hρρ1 hρ1`. Rewrite using `[key ρ le_rfl hρρ1, key ρ1 hρρ1 le_rfl, hconst, div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_pos hρ1pos _).ne']`.
-/
theorem normR_eq_of_mult_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) {ρ ρ1 : ℝ} (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1)
    (hρ1 : ρ1 < ρ0) : T.normR x ρ = T.normR x ρ1 * (ρ / ρ1) ^ T.lowIdx x ρ1 := by
  set ρ2 := (ρ1 + (ρ0 : ℝ)) / 2 with hρ2
  have hρ2a : ρ1 < ρ2 := by rw [hρ2]; linarith
  have hρ2b : ρ2 ≤ ρ0 := by rw [hρ2]; linarith
  have hρ1pos : 0 < ρ1 := hρ.trans_le hρρ1
  obtain ⟨c, hc⟩ := T.exists_approx_norm hx ⟨ρ, hρ, (hρρ1.trans hρ1.le)⟩
    ⟨ρ2, by linarith, hρ2b⟩ (show ρ ≤ ρ2 by linarith)
  have key : ∀ σ : ℝ, ρ ≤ σ → σ ≤ ρ1 → T.normR x σ =
      ‖T.coeffB c (T.lowIdx x σ)‖ * σ ^ T.lowIdx x σ := by
    intro σ h1 h2
    have hσ0 : 0 < σ := hρ.trans_le h1
    set s : Set.Ioc (0 : ℝ) ρ0 := ⟨σ, hσ0, (h2.trans hρ1.le)⟩
    have hcs := hc s h1 (by show σ ≤ ρ2; linarith)
    have hidx := T.idx_eq_of_approx hx ⟨hσ0, h2.trans_lt hρ1⟩ (η := ρ2 - σ) (by linarith)
      (by linarith) fun τ hτ1 hτ2 => hc τ (h1.trans hτ1) (by linarith)
    have hc0 : T.coeffB c ≠ 0 := by
      intro h0
      have := T.coe_ne_zero_of_approx hcs
      obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
      have hy0 : y ≠ 0 := by rintro rfl; exact this (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))
      rw [T.coeffB_eq hy] at h0
      apply hy0
      refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
      have := congrFun h0 (k - N)
      simpa using this
    rw [T.normR_eq x s, ← T.extNorm_eq_of_lt hcs, extNorm_coe, hidx.1]
    exact (lowIndex_mem hσ0 (T.convergesAt_rad ρ0 c s) hc0).symm
  have hconst := T.lowIdx_const_of_mult_zero hx h hρ hρρ1 hρ1
  rw [key ρ le_rfl hρρ1, key ρ1 hρρ1 le_rfl, hconst, div_zpow, mul_assoc,
    mul_div_assoc', mul_div_cancel_left₀ _ (zpow_pos hρ1pos _).ne']

variable [CompleteSpace L]

/- English proof (translation)
Use `set ρ1 := halfRad ρ0 with hρ1def`. Establish `hρ1v : (ρ1 : ℝ) = ρ0 / 2` using `rfl`. Establish `hρ1lt : (ρ1 : ℝ) < ρ0` using `by rw [hρ1v]; linarith [ρ0.2.1]`. Establish `hρ1pos : (0 : ℝ) < ρ1` using `ρ1.2.1`. Use `set n := T.lowIdx x ρ1 with hndef`.

Use `set x1 := T.res (halfRad_le ρ0) x with hx1`. Use `set w : T.RobbaExt ρ1 := if 0 ≤ n then T.πInvExt ρ1 ^ n.toNat else T.πExt ρ1 ^ (-n).toNat with hwdef`. Use `set wi : T.RobbaExt ρ1 := if 0 ≤ n then T.πExt ρ1 ^ n.toNat else T.πInvExt ρ1 ^ (-n).toNat with hwidef`. Establish `hwwi : w * wi = 1`. Rewrite using `[hwdef, hwidef]`.

Use `split_ifs`. Rewrite using `[← mul_pow, mul_comm, T.πExt_mul_πInvExt, one_pow]`. Rewrite using `[← mul_pow, T.πExt_mul_πInvExt, one_pow]`. Establish `hNw : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ w = (σ : ℝ) ^ (-n)`. Introduce `σ`.

Establish `hσ` using `rad_pos ρ1 σ`. Rewrite using `[hwdef]`. Use `split_ifs with hn`. Rewrite using `[extNorm_pow, extNorm_πInvExt, inv_pow, ← zpow_natCast, Int.toNat_of_nonneg hn, zpow_neg]`. Rewrite using `[extNorm_pow, extNorm_πExt, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]`.

Use `set C := T.normR x ρ1 * (ρ1 : ℝ) ^ (-n) with hC`. Establish `hC0 : 0 ≤ C`. Rewrite using `[hC, T.normR_eq x ⟨ρ1, hρ1pos, hρ1lt.le⟩]`. Conclude with `mul_nonneg (T.extNorm_nonneg _ _) (zpow_pos hρ1pos _).le`. Establish `hz : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ (x1 * w) = C`.

Introduce `σ`. Establish `hσ` using `rad_pos ρ1 σ`. Rewrite using `[extNorm_mul, hNw, hx1, T.extNorm_res, ← T.normR_eq x, T.normR_eq_of_mult_zero hx h hσ σ.2.2 hρ1lt, hC, div_zpow, zpow_neg, zpow_neg]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← hndef]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨X, hX, hres⟩` from `T.exists_gamma_of_bounded hC0 (fun σ => (hz σ).le)`. Establish `hmem : T.ofRad ρ1 (x1 * w) ∈ T.edagToTilde.range`. Use `⟨⟨algebraMap Γ T.B X, T.Econ_le_Edag _ hX⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[T.edagToTilde_apply hX]`.

Use `show T.ofRad (halfRad ρ1) (((⟨algebraMap Γ T.B X, hX⟩ : T.Econ (halfRad ρ1))) : T.RobbaExt (halfRad ρ1)) = T.ofRad ρ1 (x1 * w)`. Rewrite using `[← hres, T.ofRad_res]`. Establish `hx10 : x1 ≠ 0` using `fun h0 => hx (T.res_injective _ (h0.trans (map_zero _).symm))`. Establish `hw0 : w ≠ 0`. Introduce `h0`.

Rewrite `hwwi` using `[h0, zero_mul]`. Conclude with `zero_ne_one hwwi`. Establish `hz0 : T.ofRad ρ1 (x1 * w) ≠ 0`. Introduce `h0`. Conclude with `mul_ne_zero hx10 hw0 (T.ofRad_injective ρ1 (h0.trans (map_zero _).symm))`.

Establish `hu` using `(T.isUnit_iff _).2 ⟨hz0, hmem⟩`. Establish `hx' : T.ofRad ρ0 x = T.ofRad ρ1 (x1 * w) * T.ofRad ρ1 wi`. Rewrite using `[← map_mul, mul_assoc, hwwi, mul_one, hx1, T.ofRad_res]`. Rewrite using `[hx']`. Use `hu.mul (IsUnit.of_mul_eq_one (T.ofRad ρ1 w) ?_)` and prove the remaining obligations.

Rewrite using `[← map_mul, mul_comm, hwwi, map_one]`.
-/
theorem isUnit_ofRad_of_mult_eq_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) : IsUnit (T.ofRad ρ0 x) := by
  set ρ1 := halfRad ρ0 with hρ1def
  have hρ1v : (ρ1 : ℝ) = ρ0 / 2 := rfl
  have hρ1lt : (ρ1 : ℝ) < ρ0 := by rw [hρ1v]; linarith [ρ0.2.1]
  have hρ1pos : (0 : ℝ) < ρ1 := ρ1.2.1
  set n := T.lowIdx x ρ1 with hndef
  set x1 := T.res (halfRad_le ρ0) x with hx1
  set w : T.RobbaExt ρ1 :=
    if 0 ≤ n then T.πInvExt ρ1 ^ n.toNat else T.πExt ρ1 ^ (-n).toNat with hwdef
  set wi : T.RobbaExt ρ1 :=
    if 0 ≤ n then T.πExt ρ1 ^ n.toNat else T.πInvExt ρ1 ^ (-n).toNat with hwidef
  have hwwi : w * wi = 1 := by
    rw [hwdef, hwidef]
    split_ifs
    · rw [← mul_pow, mul_comm, T.πExt_mul_πInvExt, one_pow]
    · rw [← mul_pow, T.πExt_mul_πInvExt, one_pow]
  have hNw : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ w = (σ : ℝ) ^ (-n) := by
    intro σ
    have hσ := rad_pos ρ1 σ
    rw [hwdef]
    split_ifs with hn
    · rw [extNorm_pow, extNorm_πInvExt, inv_pow, ← zpow_natCast, Int.toNat_of_nonneg hn, zpow_neg]
    · rw [extNorm_pow, extNorm_πExt, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  set C := T.normR x ρ1 * (ρ1 : ℝ) ^ (-n) with hC
  have hC0 : 0 ≤ C := by
    rw [hC, T.normR_eq x ⟨ρ1, hρ1pos, hρ1lt.le⟩]
    exact mul_nonneg (T.extNorm_nonneg _ _) (zpow_pos hρ1pos _).le
  have hz : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ (x1 * w) = C := by
    intro σ
    have hσ := rad_pos ρ1 σ
    rw [extNorm_mul, hNw, hx1, T.extNorm_res, ← T.normR_eq x,
      T.normR_eq_of_mult_zero hx h hσ σ.2.2 hρ1lt, hC, div_zpow, zpow_neg, zpow_neg]
    field_simp
    rw [← hndef]; ring
  obtain ⟨X, hX, hres⟩ := T.exists_gamma_of_bounded hC0 (fun σ => (hz σ).le)
  have hmem : T.ofRad ρ1 (x1 * w) ∈ T.edagToTilde.range := by
    refine ⟨⟨algebraMap Γ T.B X, T.Econ_le_Edag _ hX⟩, ?_⟩
    rw [T.edagToTilde_apply hX]
    show T.ofRad (halfRad ρ1) (((⟨algebraMap Γ T.B X, hX⟩ : T.Econ (halfRad ρ1))) :
      T.RobbaExt (halfRad ρ1)) = T.ofRad ρ1 (x1 * w)
    rw [← hres, T.ofRad_res]
  have hx10 : x1 ≠ 0 := fun h0 => hx (T.res_injective _ (h0.trans (map_zero _).symm))
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hwwi; exact zero_ne_one hwwi
  have hz0 : T.ofRad ρ1 (x1 * w) ≠ 0 := by
    intro h0
    exact mul_ne_zero hx10 hw0 (T.ofRad_injective ρ1 (h0.trans (map_zero _).symm))
  have hu := (T.isUnit_iff _).2 ⟨hz0, hmem⟩
  have hx' : T.ofRad ρ0 x = T.ofRad ρ1 (x1 * w) * T.ofRad ρ1 wi := by
    rw [← map_mul, mul_assoc, hwwi, mul_one, hx1, T.ofRad_res]
  rw [hx']
  refine hu.mul (IsUnit.of_mul_eq_one (T.ofRad ρ1 w) ?_)
  rw [← map_mul, mul_comm, hwwi, map_one]

end TeichLift

end GroundTheory.PAdicHodge
