import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FloorTelescope

/- English proof (translation)
Establish `himg : Finset.Icc (-(R:ℤ)) R = (Finset.range (2*R+1)).image (fun k : ℕ => (k:ℤ) - R)`. Use extensionality with `d`. Simplify using `only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨(d + R).toNat, by omega, by omega⟩`. Introduce and unpack `⟨k, hk, rfl⟩`. Use linear arithmetic over natural numbers and integers. Rewrite using `[himg, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]`. Use `Finset.sum_range_sub (fun k : ℕ => G ((k:ℤ) - R)) (2*R+1)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `congr 2 <;> push_cast <;> ring`.
-/
lemma sum_Icc_sub (G : ℤ → ℂ) (R : ℕ) :
    ∑ d ∈ Finset.Icc (-(R:ℤ)) R, (G (d+1) - G d) = G ((R:ℤ)+1) - G (-(R:ℤ)) := by
  have himg : Finset.Icc (-(R:ℤ)) R = (Finset.range (2*R+1)).image (fun k : ℕ => (k:ℤ) - R) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(d + R).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  have := Finset.sum_range_sub (fun k : ℕ => G ((k:ℤ) - R)) (2*R+1)
  convert this using 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 2; push_cast; ring
  · congr 2 <;> push_cast <;> ring

/- English proof (translation)
Establish `hsum : ∑ y ∈ Finset.range L, φ y = 0` using `by simpa [hat] using h0`. Establish `hLz : (0:ℤ) < L` using `by exact_mod_cast hL`. Take `⟨u, hu⟩ : ∃ u : ℤ → ℂ, ∀ d, u d = (z + ((L * (d / L) : ℤ) : ℂ))⁻¹` from `⟨_, fun _ => rfl⟩`. Take `⟨Φ, hΦ⟩ : ∃ Φ : ℤ → ℂ, ∀ d, Φ d = ∑ e ∈ Finset.range (d % L).toNat, φ e` from `⟨_, fun _ => rfl⟩`. Take `⟨F, hF⟩ : ∃ F : ℤ → ℂ, ∀ d, F d = Φ d * u d` from `⟨_, fun _ => rfl⟩`.

Establish `key : ∀ d : ℤ, φ d * u d = F (d+1) - F d`. Introduce `d`. Establish `hdiv` using `Int.mul_ediv_add_emod d L`. Establish `h1` using `Int.emod_nonneg d hLz.ne'`. Establish `h2` using `Int.emod_lt_of_pos d hLz`.

Establish `hcast : (((d % L).toNat : ℕ) : ZMod L) = (d : ZMod L)`. Establish `: ((((d % L).toNat : ℕ) : ℤ) : ZMod L) = ((d % L : ℤ) : ZMod L)`. Rewrite using `[Int.toNat_of_nonneg h1]`. Rewrite `this` using `[Int.cast_natCast]`. Rewrite using `[this, ZMod.intCast_mod]`.

Break down `lt_or_eq_of_le (show d % L + 1 ≤ L by omega) with hlt | heq` into its components or cases. Establish `hq : (d+1) / L = d / L`. Establish `h3 : d + 1 = (d % L + 1) + L * (d / L)` using `by omega`. Rewrite using `[h3, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]`. Establish `hr : (d+1) % L = d % L + 1`.

Use `Int.mul_ediv_add_emod (d+1) L` as an intermediate fact. Rewrite `this` using `[hq]`. Use linear arithmetic over natural numbers and integers. Establish `hu' : u (d+1) = u d` using `by rw [hu, hu, hq]`. Establish `hΦ' : Φ (d+1) = Φ d + φ d`.

Rewrite using `[hΦ, hΦ, hr, show (d % L + 1).toNat = (d % L).toNat + 1 by omega, Finset.sum_range_succ, hcast]`. Rewrite using `[hF, hF, hu', hΦ']`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : (d+1) / L = d / L + 1`. Rewrite using `[show d + 1 = L * (d / L + 1) by linarith, Int.mul_ediv_cancel_left _ hLz.ne']`.

Establish `hr : (d+1) % L = 0`. Use `Int.mul_ediv_add_emod (d+1) L` as an intermediate fact. Rewrite `this` using `[hq]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΦ0 : Φ (d+1) = 0` using `by rw [hΦ, hr]; simp`.

Establish `hn : (d % L).toNat = L - 1` using `by omega`. Establish `hs` using `Finset.sum_range_succ (fun e : ℕ => φ (e : ZMod L)) (L-1)`. Rewrite `hs` using `[Nat.sub_add_cancel hL, ← hn, hcast, hsum]`. Establish `hΦd : Φ d = - φ d` using `by rw [hΦ]; linear_combination -hs`. Rewrite using `[hF, hF, hΦ0, hΦd]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfun : (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) = fun R : ℕ => F ((R:ℤ)+1) - F (-(R:ℤ))`. Use function extensionality and compare the values at `R`. Rewrite using `[← sum_Icc_sub]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[← key, hu]`. Rewrite using `[hfun]`. Use `set M : ℝ := ∑ y ∈ Finset.range L, ‖φ y‖`. Establish `hM : ∀ d, ‖Φ d‖ ≤ M`. Introduce `d`.

Rewrite using `[hΦ]`. Establish `h2` using `Int.emod_lt_of_pos d hLz`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _))` and prove the remaining obligations. Establish `uLim : ∀ m : ℕ → ℤ, (∀ R : ℕ, (R:ℝ) - L ≤ |((m R : ℤ) : ℝ)|) → Tendsto (fun R : ℕ => (z + ((m R : ℤ) : ℂ))⁻¹) atTop (𝓝 0)`. Introduce `m hm`.

Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [norm_inv]`. Apply `Tendsto.inv_tendsto_atTop` to reduce the goal to its premises. Use `tendsto_atTop_mono (fun R => ?_) (tendsto_atTop_add_const_right _ (-(L:ℝ) - ‖z‖) tendsto_natCast_atTop_atTop)` and prove the remaining obligations. Establish `h1 : ‖((m R : ℤ) : ℂ)‖ ≤ ‖z + ((m R : ℤ) : ℂ)‖ + ‖z‖`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[Complex.norm_intCast]`. Combine the linear relations using `[hm R]`. Establish `hFb : ∀ x, ‖F x‖ ≤ M * ‖(z + ((L * (x / L) : ℤ) : ℂ))⁻¹‖`. Introduce `x`.

Rewrite using `[hF, norm_mul, ← hu]`. Conclude with `mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)`. Establish `hA : Tendsto (fun R : ℕ => F ((R:ℤ)+1)) atTop (𝓝 0)`. Use `squeeze_zero_norm (fun R => hFb _) ?_` and prove the remaining obligations. Establish `hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * (((R:ℤ)+1) / L) : ℤ)) : ℝ)|`.

Introduce `R`. Establish `e1` using `Int.mul_ediv_add_emod ((R:ℤ)+1) L`. Establish `e2` using `Int.emod_lt_of_pos ((R:ℤ)+1) hLz`. Establish `: (R:ℤ) - L ≤ L * (((R:ℤ)+1) / L)` using `by linarith`. Use `(Int.cast_le (R := ℝ)).2 this` as an intermediate fact.

Rewrite `this` using `[Int.cast_sub, Int.cast_natCast, Int.cast_natCast]`. Conclude with `this.trans (le_abs_self _)`. Simplify `((uLim _ hm).norm.const_mul M)` using `only [norm_zero, mul_zero]`. Establish `hB : Tendsto (fun R : ℕ => F (-(R:ℤ))) atTop (𝓝 0)`. Use `squeeze_zero_norm (fun R => hFb _) ?_` and prove the remaining obligations.

Establish `hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * ((-(R:ℤ)) / L) : ℤ)) : ℝ)|`. Introduce `R`. Establish `e1` using `Int.mul_ediv_add_emod (-(R:ℤ)) L`. Establish `e2` using `Int.emod_nonneg (-(R:ℤ)) hLz.ne'`. Establish `: (R:ℤ) - L ≤ -(L * ((-(R:ℤ)) / L))` using `by linarith`.

Use `(Int.cast_le (R := ℝ)).2 this` as an intermediate fact. Rewrite `this` using `[Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_neg]`. Conclude with `this.trans (neg_le_abs _)`. Simplify `((uLim _ hm).norm.const_mul M)` using `only [norm_zero, mul_zero]`. Simplify using `using hA.sub hB`.
-/
theorem tendsto_sum_Icc_div (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hL : 0 < L) (hz : 0 < z.im)
    (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) atTop (𝓝 0) := by
  have hsum : ∑ y ∈ Finset.range L, φ y = 0 := by simpa [hat] using h0
  have hLz : (0:ℤ) < L := by exact_mod_cast hL
  obtain ⟨u, hu⟩ : ∃ u : ℤ → ℂ, ∀ d, u d = (z + ((L * (d / L) : ℤ) : ℂ))⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ → ℂ, ∀ d, Φ d = ∑ e ∈ Finset.range (d % L).toNat, φ e := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℂ, ∀ d, F d = Φ d * u d := ⟨_, fun _ => rfl⟩
  have key : ∀ d : ℤ, φ d * u d = F (d+1) - F d := by
    intro d
    have hdiv := Int.mul_ediv_add_emod d L
    have h1 := Int.emod_nonneg d hLz.ne'
    have h2 := Int.emod_lt_of_pos d hLz
    have hcast : (((d % L).toNat : ℕ) : ZMod L) = (d : ZMod L) := by
      have : ((((d % L).toNat : ℕ) : ℤ) : ZMod L) = ((d % L : ℤ) : ZMod L) := by
        rw [Int.toNat_of_nonneg h1]
      rw [Int.cast_natCast] at this
      rw [this, ZMod.intCast_mod]
    rcases lt_or_eq_of_le (show d % L + 1 ≤ L by omega) with hlt | heq
    · have hq : (d+1) / L = d / L := by
        have h3 : d + 1 = (d % L + 1) + L * (d / L) := by omega
        rw [h3, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
      have hr : (d+1) % L = d % L + 1 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; omega
      have hu' : u (d+1) = u d := by rw [hu, hu, hq]
      have hΦ' : Φ (d+1) = Φ d + φ d := by
        rw [hΦ, hΦ, hr, show (d % L + 1).toNat = (d % L).toNat + 1 by omega, Finset.sum_range_succ, hcast]
      rw [hF, hF, hu', hΦ']; ring
    · have hq : (d+1) / L = d / L + 1 := by
        rw [show d + 1 = L * (d / L + 1) by linarith, Int.mul_ediv_cancel_left _ hLz.ne']
      have hr : (d+1) % L = 0 := by
        have := Int.mul_ediv_add_emod (d+1) L
        rw [hq] at this; linarith
      have hΦ0 : Φ (d+1) = 0 := by rw [hΦ, hr]; simp
      have hn : (d % L).toNat = L - 1 := by omega
      have hs := Finset.sum_range_succ (fun e : ℕ => φ (e : ZMod L)) (L-1)
      rw [Nat.sub_add_cancel hL, ← hn, hcast, hsum] at hs
      have hΦd : Φ d = - φ d := by rw [hΦ]; linear_combination -hs
      rw [hF, hF, hΦ0, hΦd]; ring
  have hfun : (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹)
      = fun R : ℕ => F ((R:ℤ)+1) - F (-(R:ℤ)) := by
    funext R
    rw [← sum_Icc_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← key, hu]
  rw [hfun]
  set M : ℝ := ∑ y ∈ Finset.range L, ‖φ y‖
  have hM : ∀ d, ‖Φ d‖ ≤ M := by
    intro d
    rw [hΦ]
    have h2 := Int.emod_lt_of_pos d hLz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _))
  have uLim : ∀ m : ℕ → ℤ, (∀ R : ℕ, (R:ℝ) - L ≤ |((m R : ℤ) : ℝ)|) →
      Tendsto (fun R : ℕ => (z + ((m R : ℤ) : ℂ))⁻¹) atTop (𝓝 0) := by
    intro m hm
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    apply Tendsto.inv_tendsto_atTop
    refine tendsto_atTop_mono (fun R => ?_)
      (tendsto_atTop_add_const_right _ (-(L:ℝ) - ‖z‖) tendsto_natCast_atTop_atTop)
    have h1 : ‖((m R : ℤ) : ℂ)‖ ≤ ‖z + ((m R : ℤ) : ℂ)‖ + ‖z‖ := by
      calc ‖((m R : ℤ) : ℂ)‖ = ‖(z + ((m R : ℤ) : ℂ)) - z‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_intCast] at h1
    linarith [hm R]
  have hFb : ∀ x, ‖F x‖ ≤ M * ‖(z + ((L * (x / L) : ℤ) : ℂ))⁻¹‖ := by
    intro x
    rw [hF, norm_mul, ← hu]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hA : Tendsto (fun R : ℕ => F ((R:ℤ)+1)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * (((R:ℤ)+1) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod ((R:ℤ)+1) L
      have e2 := Int.emod_lt_of_pos ((R:ℤ)+1) hLz
      have : (R:ℤ) - L ≤ L * (((R:ℤ)+1) / L) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
      exact this.trans (le_abs_self _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  have hB : Tendsto (fun R : ℕ => F (-(R:ℤ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun R => hFb _) ?_
    have hm : ∀ R : ℕ, (R:ℝ) - L ≤ |(((L * ((-(R:ℤ)) / L) : ℤ)) : ℝ)| := by
      intro R
      have e1 := Int.mul_ediv_add_emod (-(R:ℤ)) L
      have e2 := Int.emod_nonneg (-(R:ℤ)) hLz.ne'
      have : (R:ℤ) - L ≤ -(L * ((-(R:ℤ)) / L)) := by linarith
      have := (Int.cast_le (R := ℝ)).2 this
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_neg] at this
      exact this.trans (neg_le_abs _)
    simpa only [norm_zero, mul_zero] using ((uLim _ hm).norm.const_mul M)
  simpa using hA.sub hB

end GlobalTheory.FloorTelescope
