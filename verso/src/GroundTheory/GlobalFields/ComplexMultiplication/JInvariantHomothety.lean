import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationEisenstein

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Establish `hmem : ∀ l ∈ L.lattice, c * l ∈ L'.lattice` using `fun l hl ↦ by`. Establish `: c * l ∈ (L'.lattice : Set ℂ)` using `by rw [h]; exact ⟨l, hl, rfl⟩`. Conclude with `this`. Establish `hmem' : ∀ l ∈ L'.lattice, c⁻¹ * l ∈ L.lattice` using `fun l hl ↦ by`. Establish `: l ∈ (c * ·) '' (L.lattice : Set ℂ)` using `by rw [← h]; exact hl`.

Take `⟨m, hm, rfl⟩` from `this`. Rewrite using `[inv_mul_cancel_left₀ hc]` and apply the resulting hypothesis. Set `e : L.lattice ≃ L'.lattice` to `{ toFun := fun l ↦ ⟨c * l, hmem _ l.2⟩ invFun := fun l ↦ ⟨c⁻¹ * l, hmem' _ l.2⟩ left_inv := fun l ↦ by ext; simp [hc] right_inv := fun l ↦ by ext; simp [hc] }`. Rewrite using `[PeriodPair.G, PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left]`. Use `tsum_congr fun l ↦ ?_` and prove the remaining obligations.

Use `show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹`. Rewrite using `[mul_pow, mul_inv]`.
-/
theorem G_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) (n : ℕ) :
    L'.G n = (c ^ n)⁻¹ * L.G n := by
  have hmem : ∀ l ∈ L.lattice, c * l ∈ L'.lattice := fun l hl ↦ by
    have : c * l ∈ (L'.lattice : Set ℂ) := by rw [h]; exact ⟨l, hl, rfl⟩
    exact this
  have hmem' : ∀ l ∈ L'.lattice, c⁻¹ * l ∈ L.lattice := fun l hl ↦ by
    have : l ∈ (c * ·) '' (L.lattice : Set ℂ) := by rw [← h]; exact hl
    obtain ⟨m, hm, rfl⟩ := this
    rwa [inv_mul_cancel_left₀ hc]
  let e : L.lattice ≃ L'.lattice :=
    { toFun := fun l ↦ ⟨c * l, hmem _ l.2⟩
      invFun := fun l ↦ ⟨c⁻¹ * l, hmem' _ l.2⟩
      left_inv := fun l ↦ by ext; simp [hc]
      right_inv := fun l ↦ by ext; simp [hc] }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

/- English proof (translation)
Rewrite using `[discr, discr, h₂, h₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma discr_of_g₂_g₃ {L L' : PeriodPair} {t : ℂ} (h₂ : L'.g₂ = t ^ 4 * L.g₂)
    (h₃ : L'.g₃ = t ^ 6 * L.g₃) : discr L' = t ^ 12 * discr L := by
  rw [discr, discr, h₂, h₃]
  ring

/- English proof (translation)
Rewrite using `[weierstrassCurve_j, weierstrassCurve_j, discr_of_g₂_g₃ h₂ h₃, h₂, show 1728 * (t ^ 4 * L.g₂) ^ 3 = t ^ 12 * (1728 * L.g₂ ^ 3) by ring, mul_div_mul_left _ _ (pow_ne_zero _ ht)]`.
-/
lemma weierstrassCurve_j_eq_of_g₂_g₃ {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (h₂ : L'.g₂ = t ^ 4 * L.g₂) (h₃ : L'.g₃ = t ^ 6 * L.g₃) :
    (weierstrassCurve L).j = (weierstrassCurve L').j := by
  rw [weierstrassCurve_j, weierstrassCurve_j, discr_of_g₂_g₃ h₂ h₃, h₂,
    show 1728 * (t ^ 4 * L.g₂) ^ 3 = t ^ 12 * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ ht)]

/- English proof (translation)
Take `⟨ε, hε, h⟩` from `Metric.mem_nhds_iff.1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)`. Use `⟨ε, hε, fun l hl h0 ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `h (mem_ball_zero_iff.2 (not_le.1 hlt))` as an intermediate fact. Conclude with `this ⟨hl, h0⟩`.
-/
lemma exists_pos_le_norm (L : PeriodPair) : ∃ ε > 0, ∀ l ∈ L.lattice, l ≠ 0 → ε ≤ ‖l‖ := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  refine ⟨ε, hε, fun l hl h0 ↦ ?_⟩
  by_contra hlt
  have := h (mem_ball_zero_iff.2 (not_le.1 hlt))
  exact this ⟨hl, h0⟩

/- English proof (translation)
Break down `Nat.even_or_odd' j with ⟨n, rfl | rfl⟩` into its components or cases. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[weierstrassLaurentCoeff]`. Rewrite using `[weierstrassLaurentCoeff_two_mul (L := L') hn, weierstrassLaurentCoeff_two_mul (L := L) hn, show 2 * n + 2 = 2 * (n + 1) by ring, hG (n + 1) (by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[weierstrassLaurentCoeff_odd, weierstrassLaurentCoeff_odd, mul_zero]`.
-/
lemma weierstrassLaurentCoeff_eq_of_G_eq {L L' : PeriodPair} {t : ℂ}
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) (j : ℕ) :
    weierstrassLaurentCoeff L' j = t ^ (j + 2) * weierstrassLaurentCoeff L j := by
  rcases Nat.even_or_odd' j with ⟨n, rfl | rfl⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [weierstrassLaurentCoeff]
    rw [weierstrassLaurentCoeff_two_mul (L := L') hn, weierstrassLaurentCoeff_two_mul (L := L) hn,
      show 2 * n + 2 = 2 * (n + 1) by ring, hG (n + 1) (by omega)]
    ring
  · rw [weierstrassLaurentCoeff_odd, weierstrassLaurentCoeff_odd, mul_zero]

/- English proof (translation)
Establish `h1` using `hasSum_weierstrassP_laurent (L := L') hz'`. Establish `h2` using `(hasSum_weierstrassP_laurent (L := L) hz).mul_left (t ^ 2)`. Establish `h3 : HasSum (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j) (t ^ 2 * (℘[L] (t * z) - 1 / (t * z) ^ 2))`. Establish `hfun : (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j) = fun j ↦ t ^ 2 * (weierstrassLaurentCoeff L j * (t * z) ^ j)`. Use function extensionality and compare the values at `j`.

Rewrite using `[weierstrassLaurentCoeff_eq_of_G_eq hG, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Conclude with `h2`. Establish `e` using `h1.unique h3`.

Establish `e' : t ^ 2 * (1 / (t * z) ^ 2) = 1 / z ^ 2`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e - e'`.
-/
theorem weierstrassP_eq_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ} (hz0 : z ≠ 0)
    (hz' : ∀ l : L'.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖t * z‖ < ‖(l : ℂ)‖) :
    ℘[L'] z = t ^ 2 * ℘[L] (t * z) := by
  have h1 := hasSum_weierstrassP_laurent (L := L') hz'
  have h2 := (hasSum_weierstrassP_laurent (L := L) hz).mul_left (t ^ 2)
  have h3 : HasSum (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j)
      (t ^ 2 * (℘[L] (t * z) - 1 / (t * z) ^ 2)) := by
    have hfun : (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j) =
        fun j ↦ t ^ 2 * (weierstrassLaurentCoeff L j * (t * z) ^ j) := by
      funext j
      rw [weierstrassLaurentCoeff_eq_of_G_eq hG, mul_pow]
      ring
    rw [hfun]
    exact h2
  have e := h1.unique h3
  have e' : t ^ 2 * (1 / (t * z) ^ 2) = 1 / z ^ 2 := by
    field_simp
  linear_combination e - e'

/- English proof (translation)
Take `⟨ε', hε', hL'⟩` from `exists_pos_le_norm L'`. Take `⟨ε, hε, hL⟩` from `exists_pos_le_norm L`. Establish `htn : 0 < ‖t‖` using `norm_pos_iff.2 ht`. Use `set ρ := min ε' (ε / ‖t‖) with hρ`. Establish `hρ0 : 0 < ρ` using `lt_min hε' (div_pos hε htn)`.

Use `set S : Set ℂ := (L'.lattice : Set ℂ) ∪ (fun w ↦ t * w) ⁻¹' L.lattice with hS`. Establish `hcount : ∀ L₀ : PeriodPair, (L₀.lattice : Set ℂ).Countable` using `fun L₀ ↦ by`. Establish `: Countable L₀.lattice` using `L₀.latticeEquivProd.injective.countable`. Conclude with `Set.countable_coe_iff.1 this`. Establish `hScount : S.Countable` using `(hcount L').union ((hcount L).preimage (mul_right_injective₀ ht))`.

Establish `hSclosed : IsClosed S` using `L'.isClosed_lattice.union (L.isClosed_lattice.preimage (continuous_const.mul continuous_id))`. Establish `hU : IsPreconnected Sᶜ`. Establish `h2 : 1 < Module.rank ℝ ℂ` using `by rw [Complex.rank_real_complex]; norm_num`. Conclude with `(hScount.isPathConnected_compl_of_one_lt_rank h2).isConnected.isPreconnected`. Establish `hf : AnalyticOnNhd ℂ ℘[L'] Sᶜ` using `fun w hw ↦ L'.analyticOnNhd_weierstrassP w fun h ↦ hw (Or.inl h)`.

Establish `hgat : ∀ w, t * w ∉ L.lattice → AnalyticAt ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) w` using `fun w hw ↦ analyticAt_const.mul ((L.analyticOnNhd_weierstrassP (t * w) hw).comp (by fun_prop))`. Establish `hg : AnalyticOnNhd ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ` using `fun w hw ↦ hgat w fun h ↦ hw (Or.inr h)`. Establish `hsmall : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → w ∈ Sᶜ ∧ ℘[L'] w = t ^ 2 * ℘[L] (t * w)`. Introduce `w hw0 hw`. Establish `hw1 : ‖w‖ < ε'` using `hw.trans_le (min_le_left _ _)`.

Establish `hw2 : ‖t * w‖ < ε`. Establish `: ‖w‖ < ε / ‖t‖` using `hw.trans_le (min_le_right _ _)`. Rewrite using `[norm_mul]`. Rewrite `this` using `[lt_div_iff₀ htn]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨?_, weierstrassP_eq_of_G_eq ht hG hw0 (fun l hl ↦ hw1.trans_le (hL' _ l.2 hl)) (fun l hl ↦ hw2.trans_le (hL _ l.2 hl))⟩` and prove the remaining obligations. Introduce and unpack `(h | h)`. Conclude with `absurd (hL' w h hw0) (not_le.2 hw1)`. Conclude with `absurd (hL (t * w) h (mul_ne_zero ht hw0)) (not_le.2 hw2)`. Use `set z₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) with hz₀`.

Establish `hz₀n : ‖z₀‖ = ρ / 2`. Rewrite using `[hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Establish `hz₀0 : z₀ ≠ 0`. Introduce `h`. Rewrite `hz₀n` using `[h, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz₀ρ : ‖z₀‖ < ρ` using `by rw [hz₀n]; linarith`. Establish `hopen : IsOpen {w : ℂ | w ≠ 0 ∧ ‖w‖ < ρ}` using `isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)`. Establish `hev : ℘[L'] =ᶠ[𝓝 z₀] fun w ↦ t ^ 2 * ℘[L] (t * w)` using `by filter_upwards [hopen.mem_nhds ⟨hz₀0, hz₀ρ⟩] with w hw`. Conclude with `(hsmall w hw.1 hw.2).2`.

Establish `hEq : EqOn ℘[L'] (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ` using `hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hsmall z₀ hz₀0 hz₀ρ).1 hev`. Assume the negation of the conclusion as `hnot`. Establish `hpunct : ℘[L'] =ᶠ[𝓝[≠] z] fun w ↦ t ^ 2 * ℘[L] (t * w)`. Establish `hclosed : IsClosed ((fun w ↦ t * w) ⁻¹' (L.lattice : Set ℂ))` using `L.isClosed_lattice.preimage (continuous_const.mul continuous_id)`. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds z), nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hnot)] with w hwz hw1 hw2`.

Use `hEq ?_` and prove the remaining obligations. Introduce and unpack `(h | h)`. Conclude with `hw1 ⟨h, hwz⟩`. Conclude with `hw2 h`. Establish `hord` using `meromorphicOrderAt_congr hpunct`.

Rewrite `hord` using `[L'.order_weierstrassP z hz]`. Establish `hnn` using `(hgat z hnot).meromorphicOrderAt_nonneg`. Rewrite `hnn` using `[← hord]`. Conclude with `absurd hnn (by decide)`.
-/
theorem mul_mem_lattice_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ}
    (hz : z ∈ L'.lattice) : t * z ∈ L.lattice := by
  obtain ⟨ε', hε', hL'⟩ := exists_pos_le_norm L'
  obtain ⟨ε, hε, hL⟩ := exists_pos_le_norm L
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  set ρ := min ε' (ε / ‖t‖) with hρ
  have hρ0 : 0 < ρ := lt_min hε' (div_pos hε htn)

  set S : Set ℂ := (L'.lattice : Set ℂ) ∪ (fun w ↦ t * w) ⁻¹' L.lattice with hS
  have hcount : ∀ L₀ : PeriodPair, (L₀.lattice : Set ℂ).Countable := fun L₀ ↦ by
    have : Countable L₀.lattice := L₀.latticeEquivProd.injective.countable
    exact Set.countable_coe_iff.1 this
  have hScount : S.Countable :=
    (hcount L').union ((hcount L).preimage (mul_right_injective₀ ht))
  have hSclosed : IsClosed S :=
    L'.isClosed_lattice.union (L.isClosed_lattice.preimage (continuous_const.mul continuous_id))
  have hU : IsPreconnected Sᶜ := by
    have h2 : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact (hScount.isPathConnected_compl_of_one_lt_rank h2).isConnected.isPreconnected
  have hf : AnalyticOnNhd ℂ ℘[L'] Sᶜ := fun w hw ↦
    L'.analyticOnNhd_weierstrassP w fun h ↦ hw (Or.inl h)
  have hgat : ∀ w, t * w ∉ L.lattice → AnalyticAt ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) w := fun w hw ↦
    analyticAt_const.mul ((L.analyticOnNhd_weierstrassP (t * w) hw).comp (by fun_prop))
  have hg : AnalyticOnNhd ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ := fun w hw ↦
    hgat w fun h ↦ hw (Or.inr h)

  have hsmall : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → w ∈ Sᶜ ∧ ℘[L'] w = t ^ 2 * ℘[L] (t * w) := by
    intro w hw0 hw
    have hw1 : ‖w‖ < ε' := hw.trans_le (min_le_left _ _)
    have hw2 : ‖t * w‖ < ε := by
      have : ‖w‖ < ε / ‖t‖ := hw.trans_le (min_le_right _ _)
      rw [norm_mul]
      rw [lt_div_iff₀ htn] at this
      linarith
    refine ⟨?_, weierstrassP_eq_of_G_eq ht hG hw0 (fun l hl ↦ hw1.trans_le (hL' _ l.2 hl))
      (fun l hl ↦ hw2.trans_le (hL _ l.2 hl))⟩
    rintro (h | h)
    · exact absurd (hL' w h hw0) (not_le.2 hw1)
    · exact absurd (hL (t * w) h (mul_ne_zero ht hw0)) (not_le.2 hw2)
  set z₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) with hz₀
  have hz₀n : ‖z₀‖ = ρ / 2 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz₀0 : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀n
    linarith
  have hz₀ρ : ‖z₀‖ < ρ := by rw [hz₀n]; linarith
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ ‖w‖ < ρ} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : ℘[L'] =ᶠ[𝓝 z₀] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    filter_upwards [hopen.mem_nhds ⟨hz₀0, hz₀ρ⟩] with w hw
    exact (hsmall w hw.1 hw.2).2
  have hEq : EqOn ℘[L'] (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hsmall z₀ hz₀0 hz₀ρ).1 hev

  by_contra hnot
  have hpunct : ℘[L'] =ᶠ[𝓝[≠] z] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    have hclosed : IsClosed ((fun w ↦ t * w) ⁻¹' (L.lattice : Set ℂ)) :=
      L.isClosed_lattice.preimage (continuous_const.mul continuous_id)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds z),
      nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hnot)] with w hwz hw1 hw2
    refine hEq ?_
    rintro (h | h)
    · exact hw1 ⟨h, hwz⟩
    · exact hw2 h
  have hord := meromorphicOrderAt_congr hpunct
  rw [L'.order_weierstrassP z hz] at hord
  have hnn := (hgat z hnot).meromorphicOrderAt_nonneg
  rw [← hord] at hnn
  exact absurd hnn (by decide)

/- English proof (translation)
Establish `hG' : ∀ k, 2 ≤ k → L.G (2 * k) = t⁻¹ ^ (2 * k) * L'.G (2 * k)` using `fun k hk ↦ by`. Rewrite using `[hG k hk, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ ht)]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Conclude with `⟨t * z, mul_mem_lattice_of_G_eq ht hG hz, by simp [ht]⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `mul_mem_lattice_of_G_eq (inv_ne_zero ht) hG' hw`.
-/
theorem lattice_eq_of_G_eq {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) :
    (L'.lattice : Set ℂ) = (t⁻¹ * ·) '' L.lattice := by
  have hG' : ∀ k, 2 ≤ k → L.G (2 * k) = t⁻¹ ^ (2 * k) * L'.G (2 * k) := fun k hk ↦ by
    rw [hG k hk, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ ht)]
  ext z
  constructor
  · intro hz
    exact ⟨t * z, mul_mem_lattice_of_G_eq ht hG hz, by simp [ht]⟩
  · rintro ⟨w, hw, rfl⟩
    exact mul_mem_lattice_of_G_eq (inv_ne_zero ht) hG' hw

/- English proof (translation)
Establish `hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0` using `(C.u⁻¹).ne_zero`. Establish `h1` using `congrArg WeierstrassCurve.a₁ hC`. Establish `h2` using `congrArg WeierstrassCurve.a₂ hC`. Establish `h3` using `congrArg WeierstrassCurve.a₃ hC`. Establish `h4` using `congrArg WeierstrassCurve.a₄ hC`.

Establish `h6` using `congrArg WeierstrassCurve.a₆ hC`. Rewrite `h1` using `[WeierstrassCurve.variableChange_a₁]`. Rewrite `h2` using `[WeierstrassCurve.variableChange_a₂]`. Rewrite `h3` using `[WeierstrassCurve.variableChange_a₃]`. Rewrite `h4` using `[WeierstrassCurve.variableChange_a₄]`.

Rewrite `h6` using `[WeierstrassCurve.variableChange_a₆]`. Simplify using `only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄, weierstrassCurve_a₆] at h1 h2 h3 h4 h6`. Establish `hs : C.s = 0`. Use `(mul_eq_zero.1 h1).resolve_left hu` as an intermediate fact. Take the linear combination `this / 2`.

Establish `ht : C.t = 0`. Use `(mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ hu)` as an intermediate fact. Take the linear combination `this / 2`. Establish `hr : C.r = 0`. Use `(mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hu)` as an intermediate fact.

Rewrite `this` using `[hs]`. Take the linear combination `this / 3`. Rewrite `h4` using `[hs, ht, hr]`. Rewrite `h6` using `[ht, hr]`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `4 * h4`. Take the linear combination `4 * h6`.
-/
lemma g₂_g₃_of_variableChange {L L' : PeriodPair} {C : WeierstrassCurve.VariableChange ℂ}
    (hC : C • weierstrassCurve L = weierstrassCurve L') :
    L'.g₂ = ((C.u⁻¹ : ℂˣ) : ℂ) ^ 4 * L.g₂ ∧ L'.g₃ = ((C.u⁻¹ : ℂˣ) : ℂ) ^ 6 * L.g₃ := by
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := (C.u⁻¹).ne_zero
  have h1 := congrArg WeierstrassCurve.a₁ hC
  have h2 := congrArg WeierstrassCurve.a₂ hC
  have h3 := congrArg WeierstrassCurve.a₃ hC
  have h4 := congrArg WeierstrassCurve.a₄ hC
  have h6 := congrArg WeierstrassCurve.a₆ hC
  rw [WeierstrassCurve.variableChange_a₁] at h1
  rw [WeierstrassCurve.variableChange_a₂] at h2
  rw [WeierstrassCurve.variableChange_a₃] at h3
  rw [WeierstrassCurve.variableChange_a₄] at h4
  rw [WeierstrassCurve.variableChange_a₆] at h6
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆] at h1 h2 h3 h4 h6
  have hs : C.s = 0 := by
    have := (mul_eq_zero.1 h1).resolve_left hu
    linear_combination this / 2
  have ht : C.t = 0 := by
    have := (mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ hu)
    linear_combination this / 2
  have hr : C.r = 0 := by
    have := (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hu)
    rw [hs] at this
    linear_combination this / 3
  rw [hs, ht, hr] at h4
  rw [ht, hr] at h6
  constructor
  · linear_combination 4 * h4
  · linear_combination 4 * h6

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hj`. Take `⟨C, hC⟩` from `WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj`. Take `⟨h₂, h₃⟩` from `g₂_g₃_of_variableChange hC`. Use `set t : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)`.

Establish `ht : t ≠ 0` using `(C.u⁻¹).ne_zero`. Establish `hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)` using `fun k hk ↦ G_eq_of_g₂_g₃ (L := L) h₂ h₃ hk`. Conclude with `⟨t⁻¹, inv_ne_zero ht, lattice_eq_of_G_eq ht hG⟩`. Introduce and unpack `⟨c, hc, h⟩`. Establish `hG` using `G_eq_of_lattice_eq_smul hc h`.

Use `weierstrassCurve_j_eq_of_g₂_g₃ (t := c⁻¹) (inv_ne_zero hc) ?_ ?_` and prove the remaining obligations. Rewrite using `[PeriodPair.g₂, PeriodPair.g₂, hG, inv_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[PeriodPair.g₃, PeriodPair.g₃, hG, inv_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrassCurve_j_eq_iff {L L' : PeriodPair} :
    (weierstrassCurve L).j = (weierstrassCurve L').j ↔
      ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  constructor
  · intro hj
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
    obtain ⟨h₂, h₃⟩ := g₂_g₃_of_variableChange hC
    set t : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)
    have ht : t ≠ 0 := (C.u⁻¹).ne_zero
    have hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k) := fun k hk ↦
      G_eq_of_g₂_g₃ (L := L) h₂ h₃ hk
    exact ⟨t⁻¹, inv_ne_zero ht, lattice_eq_of_G_eq ht hG⟩
  · rintro ⟨c, hc, h⟩
    have hG := G_eq_of_lattice_eq_smul hc h
    refine weierstrassCurve_j_eq_of_g₂_g₃ (t := c⁻¹) (inv_ne_zero hc) ?_ ?_
    · rw [PeriodPair.g₂, PeriodPair.g₂, hG, inv_pow]
      ring
    · rw [PeriodPair.g₃, PeriodPair.g₃, hG, inv_pow]
      ring

/- English proof (translation)
Rewrite using `[← weierstrassCurve_latticeOfTau_j, ← weierstrassCurve_latticeOfTau_j, weierstrassCurve_j_eq_iff]`.
-/
theorem modularJ_eq_iff (τ τ' : UpperHalfPlane) :
    modularJ τ = modularJ τ' ↔ ∃ c : ℂ, c ≠ 0 ∧
      ((latticeOfTau τ').lattice : Set ℂ) = (c * ·) '' (latticeOfTau τ).lattice := by
  rw [← weierstrassCurve_latticeOfTau_j, ← weierstrassCurve_latticeOfTau_j, weierstrassCurve_j_eq_iff]

end Elliptic
end GroundTheory.Global
