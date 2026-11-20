import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open PowerSeries GlobalTheory.MomOne Filter PeriodPair
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.UW

variable {q : ℕ} [Fact q.Prime] (M : Mdl q)

/- English proof (translation)
Take `⟨hc, -, -, -, -, -, -, h4, -⟩` from `h`. Establish `hc4` using `congrArg M.ι.symm h4`. Simplify using `only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, map_sub, map_add, map_mul, map_pow, map_ofNat] at hc4`. Establish `hc0 : M.c ^ 4 ≠ 0` using `pow_ne_zero 4 hc`. Clear denominators, using `at hc4 ⊢` for the nonvanishing conditions.

Take the linear combination `-hc4`.
-/
lemma g₂_eq (h : M.Ok) : M.L.g₂ = M.c ^ 4 * (((M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) ^ 2 -
    24 * (2 * M.ι.symm M.W.a₄ + M.ι.symm M.W.a₁ * M.ι.symm M.W.a₃)) / 12) := by
  obtain ⟨hc, -, -, -, -, -, -, h4, -⟩ := h
  have hc4 := congrArg M.ι.symm h4
  simp only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, map_sub, map_add, map_mul, map_pow, map_ofNat] at hc4
  have hc0 : M.c ^ 4 ≠ 0 := pow_ne_zero 4 hc
  field_simp at hc4 ⊢
  linear_combination -hc4

/- English proof (translation)
Take `⟨hc, -, -, -, -, -, -, -, h6⟩` from `h`. Establish `hc6` using `congrArg M.ι.symm h6`. Simplify using `only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg] at hc6`. Establish `hc0 : M.c ^ 6 ≠ 0` using `pow_ne_zero 6 hc`. Clear denominators, using `at hc6 ⊢` for the nonvanishing conditions.

Take the linear combination `-hc6`.
-/
lemma g₃_eq (h : M.Ok) : M.L.g₃ = M.c ^ 6 * ((-(M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) ^ 3 +
    36 * (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) *
      (2 * M.ι.symm M.W.a₄ + M.ι.symm M.W.a₁ * M.ι.symm M.W.a₃) -
    216 * (M.ι.symm M.W.a₃ ^ 2 + 4 * M.ι.symm M.W.a₆)) / 216) := by
  obtain ⟨hc, -, -, -, -, -, -, -, h6⟩ := h
  have hc6 := congrArg M.ι.symm h6
  simp only [RingEquiv.symm_apply_apply, map_div₀, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg] at hc6
  have hc0 : M.c ^ 6 ≠ 0 := pow_ne_zero 6 hc
  field_simp at hc6 ⊢
  linear_combination -hc6

/- English proof (translation)
Simplify using `only [Mdl.x, WeierstrassCurve.b₂, map_div₀, map_add, map_mul, map_pow, map_ofNat]`.
-/
lemma x_eq (z : ℂ) : M.x z =
    ℘[M.L] z / M.c ^ 2 - (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) / 12 := by
  simp only [Mdl.x, WeierstrassCurve.b₂, map_div₀, map_add, map_mul, map_pow, map_ofNat]

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Rewrite using `[x_eq M z]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma charpoly_eq_of_isIso (h : M.Ok) (z : ℂ) : ℘[M.L] z =
    M.c ^ 2 * (M.x z + (M.ι.symm M.W.a₁ ^ 2 + 4 * M.ι.symm M.W.a₂) / 12) := by
  have hc : M.c ≠ 0 := h.1
  rw [x_eq M z]
  field_simp
  ring

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Simplify using `only [Mdl.y]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma P'_eq (h : M.Ok) (z : ℂ) : ℘'[M.L] z =
    M.c ^ 3 * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃) := by
  have hc : M.c ≠ 0 := h.1
  simp only [Mdl.y]
  field_simp
  ring

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Establish `key` using `M.L.derivWeierstrassP_sq z hz`. Rewrite `key` using `[P'_eq M h z, charpoly_eq_of_isIso M h z, g₂_eq M h, g₃_eq M h]`. Establish `h4 : (4 * M.c ^ 6) * ((M.y z ^ 2 + M.ι.symm M.W.a₁ * M.x z * M.y z + M.ι.symm M.W.a₃ * M.y z) - (M.x z ^ 3 + M.ι.symm M.W.a₂ * M.x z ^ 2 + M.ι.symm M.W.a₄ * M.x z + M.ι.symm M.W.a₆)) = 0`. Take the linear combination `key`.

Establish `h46 : (4 * M.c ^ 6) ≠ 0` using `mul_ne_zero (by norm_num) (pow_ne_zero 6 hc)`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h46)`.
-/
lemma equation (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    M.y z ^ 2 + M.ι.symm M.W.a₁ * M.x z * M.y z + M.ι.symm M.W.a₃ * M.y z =
      M.x z ^ 3 + M.ι.symm M.W.a₂ * M.x z ^ 2 + M.ι.symm M.W.a₄ * M.x z + M.ι.symm M.W.a₆ := by
  have hc : M.c ≠ 0 := h.1
  have key := M.L.derivWeierstrassP_sq z hz
  rw [P'_eq M h z, charpoly_eq_of_isIso M h z, g₂_eq M h, g₃_eq M h] at key
  have h4 : (4 * M.c ^ 6) * ((M.y z ^ 2 + M.ι.symm M.W.a₁ * M.x z * M.y z + M.ι.symm M.W.a₃ * M.y z) -
      (M.x z ^ 3 + M.ι.symm M.W.a₂ * M.x z ^ 2 + M.ι.symm M.W.a₄ * M.x z + M.ι.symm M.W.a₆)) = 0 := by
    linear_combination key
  have h46 : (4 * M.c ^ 6) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 6 hc)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h46)

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Establish `hd` using `((GlobalTheory.hasDerivAt_weierstrassP M.L hz).div_const (M.c ^ 2)).sub_const (M.ι.symm (M.W.b₂ / 12))`. Use `hd.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[P'_eq M h z]`. Clear the denominators using the available nonvanishing facts.
-/
lemma hasDerivAt_x_of_not_mem_lattice (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    HasDerivAt M.x (M.c * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃)) z := by
  have hc : M.c ≠ 0 := h.1
  have hd := ((GlobalTheory.hasDerivAt_weierstrassP M.L hz).div_const (M.c ^ 2)).sub_const (M.ι.symm (M.W.b₂ / 12))
  refine hd.congr_deriv ?_
  rw [P'_eq M h z]
  field_simp

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Establish `hx` using `hasDerivAt_x_of_not_mem_lattice M h hz`. Establish `hd` using `((((GlobalTheory.hasDerivAt_derivWeierstrassP M.L hz).div_const (M.c ^ 3)).sub (hx.const_mul (M.ι.symm M.W.a₁))).sub_const (M.ι.symm M.W.a₃)).div_const 2`. Use `hd.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[charpoly_eq_of_isIso M h z, g₂_eq M h]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_y (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) :
    HasDerivAt M.y (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ -
      M.ι.symm M.W.a₁ * M.y z)) z := by
  have hc : M.c ≠ 0 := h.1
  have hx := hasDerivAt_x_of_not_mem_lattice M h hz
  have hd := ((((GlobalTheory.hasDerivAt_derivWeierstrassP M.L hz).div_const (M.c ^ 3)).sub
    (hx.const_mul (M.ι.symm M.W.a₁))).sub_const (M.ι.symm M.W.a₃)).div_const 2
  refine hd.congr_deriv ?_
  rw [charpoly_eq_of_isIso M h z, g₂_eq M h]
  field_simp
  ring

/- English proof (translation)
Use `M.L.analyticOnNhd_weierstrassP z hz` as an intermediate fact. Use `show AnalyticAt ℂ (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)) z`. Use `fun_prop`.
-/
lemma analyticAt_x_of_not_mem_lattice {z : ℂ} (hz : z ∉ M.L.lattice) : AnalyticAt ℂ M.x z := by
  have := M.L.analyticOnNhd_weierstrassP z hz
  show AnalyticAt ℂ (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)) z
  fun_prop

/- English proof (translation)
Establish `h1` using `M.L.analyticOnNhd_derivWeierstrassP z hz`. Establish `h2` using `analyticAt_x_of_not_mem_lattice M hz`. Use `show AnalyticAt ℂ (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2) z`. Use `fun_prop`.
-/
lemma analyticAt_y {z : ℂ} (hz : z ∉ M.L.lattice) : AnalyticAt ℂ M.y z := by
  have h1 := M.L.analyticOnNhd_derivWeierstrassP z hz
  have h2 := analyticAt_x_of_not_mem_lattice M hz
  show AnalyticAt ℂ (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2) z
  fun_prop

/- English proof (translation)
Use `show Meromorphic (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12))`. Use `fun_prop`.
-/
lemma meromorphic_x : Meromorphic M.x := by
  show Meromorphic (fun t => ℘[M.L] t / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12))
  fun_prop

/- English proof (translation)
Use `meromorphic_x M` as an intermediate fact. Use `show Meromorphic (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2)`. Use `fun_prop`.
-/
lemma meromorphic_y : Meromorphic M.y := by
  have := meromorphic_x M
  show Meromorphic (fun t => (℘'[M.L] t / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x t - M.ι.symm M.W.a₃) / 2)
  fun_prop

/- English proof (translation)
Establish `hp` using `M.L.weierstrassP_add_coe z ⟨l, hl⟩`. Simplify using `only at hp`. Simplify using `only [Mdl.x, hp]`.
-/
lemma x_add {l : ℂ} (hl : l ∈ M.L.lattice) (z : ℂ) : M.x (z + l) = M.x z := by
  have hp := M.L.weierstrassP_add_coe z ⟨l, hl⟩
  simp only at hp
  simp only [Mdl.x, hp]

/- English proof (translation)
Establish `hp` using `M.L.derivWeierstrassP_add_coe z ⟨l, hl⟩`. Simplify using `only at hp`. Simplify using `only [Mdl.y, hp, x_add M hl]`.
-/
lemma y_add {l : ℂ} (hl : l ∈ M.L.lattice) (z : ℂ) : M.y (z + l) = M.y z := by
  have hp := M.L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  simp only at hp
  simp only [Mdl.y, hp, x_add M hl]

/- English proof (translation)
Use `⟨fun z₀ => ?_, fun l hl z => ?_⟩` and prove the remaining obligations. Establish `hm : MeromorphicAt (fun t => -M.x t / M.y t) z₀`. Use `meromorphic_x M z₀` as an intermediate fact. Use `meromorphic_y M z₀` as an intermediate fact. Use `fun_prop`.

Use `hm.congr ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht`. Simplify using `[Mdl.u, ht]`. Establish `hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice` using `add_mem_cancel_right hl`. Distinguish the cases in `hz : z ∈ M.L.lattice`.

Establish `hz'` using `hmem.mpr hz`. Simplify using `[Mdl.u, hz, hz']`. Establish `hz' : z + l ∉ M.L.lattice` using `fun h' => hz (hmem.mp h')`. Simplify using `[Mdl.u, hz, hz', x_add M hl, y_add M hl]`.
-/
lemma ell_u : Ell M.L M.u := by
  refine ⟨fun z₀ => ?_, fun l hl z => ?_⟩
  · have hm : MeromorphicAt (fun t => -M.x t / M.y t) z₀ := by
      have := meromorphic_x M z₀
      have := meromorphic_y M z₀
      fun_prop
    refine hm.congr ?_
    filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht
    simp [Mdl.u, ht]
  · have hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice := add_mem_cancel_right hl
    by_cases hz : z ∈ M.L.lattice
    · have hz' := hmem.mpr hz
      simp [Mdl.u, hz, hz']
    · have hz' : z + l ∉ M.L.lattice := fun h' => hz (hmem.mp h')
      simp [Mdl.u, hz, hz', x_add M hl, y_add M hl]

/- English proof (translation)
Use `⟨fun z₀ => ?_, fun l hl z => ?_⟩` and prove the remaining obligations. Establish `hm : MeromorphicAt (fun t => -1 / M.y t) z₀`. Use `meromorphic_y M z₀` as an intermediate fact. Use `fun_prop`. Use `hm.congr ?_` and prove the remaining obligations.

Use `filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht`. Simplify using `[Mdl.w, ht]`. Establish `hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice` using `add_mem_cancel_right hl`. Distinguish the cases in `hz : z ∈ M.L.lattice`. Establish `hz'` using `hmem.mpr hz`.

Simplify using `[Mdl.w, hz, hz']`. Establish `hz' : z + l ∉ M.L.lattice` using `fun h' => hz (hmem.mp h')`. Simplify using `[Mdl.w, hz, hz', y_add M hl]`.
-/
lemma ell_w : Ell M.L M.w := by
  refine ⟨fun z₀ => ?_, fun l hl z => ?_⟩
  · have hm : MeromorphicAt (fun t => -1 / M.y t) z₀ := by
      have := meromorphic_y M z₀
      fun_prop
    refine hm.congr ?_
    filter_upwards [GlobalTheory.eventually_ne_notMem_periodLattice M.L z₀] with t ht
    simp [Mdl.w, ht]
  · have hmem : z + l ∈ M.L.lattice ↔ z ∈ M.L.lattice := add_mem_cancel_right hl
    by_cases hz : z ∈ M.L.lattice
    · have hz' := hmem.mpr hz
      simp [Mdl.w, hz, hz']
    · have hz' : z + l ∉ M.L.lattice := fun h' => hz (hmem.mp h')
      simp [Mdl.w, hz, hz', y_add M hl]

/- English proof (translation)
Use `filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht`. Simplify using `[Mdl.u, ht]`.
-/
lemma u_ev {z : ℂ} (hz : z ∉ M.L.lattice) : M.u =ᶠ[𝓝 z] fun t => -M.x t / M.y t := by
  filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht
  simp [Mdl.u, ht]

/- English proof (translation)
Use `filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht`. Simplify using `[Mdl.w, ht]`.
-/
lemma w_ev {z : ℂ} (hz : z ∉ M.L.lattice) : M.w =ᶠ[𝓝 z] fun t => -1 / M.y t := by
  filter_upwards [GlobalTheory.eventually_notMem_periodLattice M.L hz] with t ht
  simp [Mdl.w, ht]

/- English proof (translation)
Establish `hx` using `analyticAt_x_of_not_mem_lattice M hz`. Establish `hy'` using `analyticAt_y M hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hx.neg.div hy' hy).congr (u_ev M hz).symm`. Conclude with `((analyticAt_const (v := (-1 : ℂ))).div hy' hy).congr (w_ev M hz).symm`.
-/
lemma analyticAt_uw {z : ℂ} (hz : z ∉ M.L.lattice) (hy : M.y z ≠ 0) :
    AnalyticAt ℂ M.u z ∧ AnalyticAt ℂ M.w z := by
  have hx := analyticAt_x_of_not_mem_lattice M hz
  have hy' := analyticAt_y M hz
  refine ⟨?_, ?_⟩
  · exact (hx.neg.div hy' hy).congr (u_ev M hz).symm
  · exact ((analyticAt_const (v := (-1 : ℂ))).div hy' hy).congr (w_ev M hz).symm

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Establish `heq` using `equation M h hz`. Establish `hinv : M.y z * (M.y z)⁻¹ = 1` using `mul_inv_cancel₀ hy`. Establish `hu : M.u z = -M.x z / M.y z` using `by simp [Mdl.u, hz]`. Establish `hw : M.w z = -1 / M.y z` using `by simp [Mdl.w, hz]`.

Establish `hx` using `hasDerivAt_x_of_not_mem_lattice M h hz`. Establish `hyd` using `hasDerivAt_y M h hz`. Establish `hdu : HasDerivAt (fun t => -M.x t / M.y t) ((-(M.c * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃)) * M.y z - (-M.x z) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z` using `hx.neg.div hyd hy`. Establish `hdw : HasDerivAt (fun t => -1 / M.y t) ((0 * M.y z - (-1) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z` using `(hasDerivAt_const z (-1 : ℂ)).div hyd hy`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hu, hw]`. Take the linear combination `(-(M.y z)⁻¹ ^ 3) * heq + ((M.y z)⁻¹ * (M.y z * (M.y z)⁻¹ + 1) + M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ ^ 2 + M.ι.symm M.W.a₃ * (M.y z)⁻¹ ^ 2) * hinv`. Rewrite using `[(u_ev M hz).deriv_eq, hdu.deriv, hu, hw]`. Take the linear combination `(-3 * M.c * (M.y z)⁻¹ ^ 2) * heq + (M.c * (M.y z * (M.y z)⁻¹ + 1) + M.c * M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ + 2 * M.c * M.ι.symm M.W.a₃ * (M.y z)⁻¹) * hinv`. Rewrite using `[(w_ev M hz).deriv_eq, hdw.deriv, hu, hw]`.

Take the linear combination `(-M.c * M.ι.symm M.W.a₁ * (M.y z)⁻¹) * hinv`.
-/
lemma flow_off (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) (hy : M.y z ≠ 0) :
    M.w z = M.u z ^ 3 + M.ι.symm M.W.a₁ * M.u z * M.w z + M.ι.symm M.W.a₂ * M.u z ^ 2 * M.w z +
      M.ι.symm M.W.a₃ * M.w z ^ 2 + M.ι.symm M.W.a₄ * M.u z * M.w z ^ 2 +
      M.ι.symm M.W.a₆ * M.w z ^ 3 ∧
    deriv M.u z = M.c * (1 - M.ι.symm M.W.a₁ * M.u z - M.ι.symm M.W.a₂ * M.u z ^ 2 -
      2 * M.ι.symm M.W.a₃ * M.w z - 2 * M.ι.symm M.W.a₄ * M.u z * M.w z -
      3 * M.ι.symm M.W.a₆ * M.w z ^ 2) ∧
    deriv M.w z = M.c * (3 * M.u z ^ 2 + M.ι.symm M.W.a₁ * M.w z +
      2 * M.ι.symm M.W.a₂ * M.u z * M.w z + M.ι.symm M.W.a₄ * M.w z ^ 2) := by
  have hc : M.c ≠ 0 := h.1
  have heq := equation M h hz
  have hinv : M.y z * (M.y z)⁻¹ = 1 := mul_inv_cancel₀ hy
  have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hz]
  have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hz]
  have hx := hasDerivAt_x_of_not_mem_lattice M h hz
  have hyd := hasDerivAt_y M h hz
  have hdu : HasDerivAt (fun t => -M.x t / M.y t)
      ((-(M.c * (2 * M.y z + M.ι.symm M.W.a₁ * M.x z + M.ι.symm M.W.a₃)) * M.y z - (-M.x z) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z := hx.neg.div hyd hy
  have hdw : HasDerivAt (fun t => -1 / M.y t) ((0 * M.y z - (-1) * (M.c * (3 * M.x z ^ 2 + 2 * M.ι.symm M.W.a₂ * M.x z + M.ι.symm M.W.a₄ - M.ι.symm M.W.a₁ * M.y z))) / M.y z ^ 2) z :=
    (hasDerivAt_const z (-1 : ℂ)).div hyd hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hu, hw]
    linear_combination (-(M.y z)⁻¹ ^ 3) * heq +
      ((M.y z)⁻¹ * (M.y z * (M.y z)⁻¹ + 1) + M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ ^ 2 +
        M.ι.symm M.W.a₃ * (M.y z)⁻¹ ^ 2) * hinv
  · rw [(u_ev M hz).deriv_eq, hdu.deriv, hu, hw]
    linear_combination (-3 * M.c * (M.y z)⁻¹ ^ 2) * heq +
      (M.c * (M.y z * (M.y z)⁻¹ + 1) + M.c * M.ι.symm M.W.a₁ * M.x z * (M.y z)⁻¹ +
        2 * M.c * M.ι.symm M.W.a₃ * (M.y z)⁻¹) * hinv
  · rw [(w_ev M hz).deriv_eq, hdw.deriv, hu, hw]
    linear_combination (-M.c * M.ι.symm M.W.a₁ * (M.y z)⁻¹) * hinv

/- English proof (translation)
Establish `hc : M.c ≠ 0` using `h.1`. Take `⟨Xt, hXdef⟩ : ∃ Xt : ℂ → ℂ, Xt = fun z => ((z - l) ^ 2 * (℘[M.L - l] z - 1 / l ^ 2) + 1) / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12) * (z - l) ^ 2` from `⟨_, rfl⟩`. Take `⟨Yt, hYdef⟩ : ∃ Yt : ℂ → ℂ, Yt = fun z => (((z - l) ^ 3 * ℘'[M.L - l] z - 2) / M.c ^ 3 - M.ι.symm M.W.a₁ * (z - l) * Xt z - M.ι.symm M.W.a₃ * (z - l) ^ 3) / 2` from `⟨_, rfl⟩`. Establish `hP0` using `M.L.analyticAt_weierstrassPExcept l`. Establish `hD0` using `M.L.analyticAt_derivWeierstrassPExcept l`.

Establish `hXt : AnalyticAt ℂ Xt l`. Rewrite using `[hXdef]`. Use `fun_prop`. Establish `hYt : AnalyticAt ℂ Yt l`. Rewrite using `[hYdef]`.

Use `fun_prop`. Establish `hXl : Xt l = 1 / M.c ^ 2`. Rewrite using `[hXdef]`. Use `beta_reduce`. Expand and normalize the polynomial expressions, which then agree.

Establish `hYl : Yt l = -1 / M.c ^ 3`. Rewrite using `[hYdef]`. Use `beta_reduce`. Expand and normalize the polynomial expressions, which then agree. Establish `hYne : Yt l ≠ 0`.

Rewrite using `[hYl]`. Conclude with `div_ne_zero (by norm_num) (pow_ne_zero 3 hc)`. Establish `hf : AnalyticAt ℂ (fun z => -Xt z / Yt z) l` using `hXt.neg.div hYt hYne`. Establish `hg : AnalyticAt ℂ (fun z => -(z - l) ^ 2 / Yt z) l`. Establish `hs : AnalyticAt ℂ (fun z => -(z - l) ^ 2) l` using `by fun_prop`.

Conclude with `hs.div hYt hYne`. Establish `hfl : -Xt l / Yt l = M.c`. Rewrite using `[hXl, hYl]`. Clear the denominators using the available nonvanishing facts. Establish `hev1 : ∀ᶠ z in 𝓝 l, Yt z ≠ 0` using `hYt.continuousAt.eventually_ne hYne`.

Establish `hev2 : ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice` using `eventually_nhdsWithin_iff.mp (GlobalTheory.eventually_ne_notMem_periodLattice M.L l)`. Use `⟨fun z => -Xt z / Yt z, fun z => -(z - l) ^ 2 / Yt z, hf, hg, hfl, by simp, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev1, hev2] with z hz1 hz2`. Distinguish the cases in `hzl : z = l`. Rewrite using `[hzl]`.

Conclude with `⟨by simp [Mdl.u, hl], by simp [Mdl.w, hl], fun h' => absurd rfl h'⟩`. Establish `hzL` using `hz2 hzl`. Establish `hs : z - l ≠ 0` using `sub_ne_zero.mpr hzl`. Establish `hP : ℘[M.L] z = ℘[M.L - l] z - 1 / l ^ 2 + 1 / (z - l) ^ 2`. Establish `e` using `M.L.weierstrassPExcept_def ⟨l, hl⟩ z`.

Take the linear combination `-e`. Establish `hD : ℘'[M.L] z = ℘'[M.L - l] z - 2 / (z - l) ^ 3`. Establish `e` using `M.L.derivWeierstrassPExcept_def ⟨l, hl⟩ z`. Take the linear combination `-e`. Establish `hx : (z - l) ^ 2 * M.x z = Xt z`.

Rewrite using `[hXdef]`. Simplify using `only [Mdl.x, hP]`. Clear the denominators using the available nonvanishing facts. Establish `hy : (z - l) ^ 3 * M.y z = Yt z`. Rewrite using `[hYdef]`.

Simplify using `only [Mdl.y, hD]`. Rewrite using `[← hx]`. Clear the denominators using the available nonvanishing facts. Establish `hy0 : M.y z ≠ 0`. Introduce `h0`.

Apply `hz1` to reduce the goal to its premises. Rewrite using `[← hy, h0, mul_zero]`. Use `⟨?_, ?_, fun _ => ⟨hzL, hy0⟩⟩` and prove the remaining obligations. Simplify using `only [Mdl.u, if_neg hzL]`. Rewrite using `[← hx, ← hy]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [Mdl.w, if_neg hzL]`. Rewrite using `[← hy]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma exists_analytic_u_w_factor_near_lattice (h : M.Ok) {l : ℂ} (hl : l ∈ M.L.lattice) :
    ∃ f g : ℂ → ℂ, AnalyticAt ℂ f l ∧ AnalyticAt ℂ g l ∧ f l = M.c ∧ g l = 0 ∧
      ∀ᶠ z in 𝓝 l, M.u z = (z - l) * f z ∧ M.w z = (z - l) * g z ∧
        (z ≠ l → z ∉ M.L.lattice ∧ M.y z ≠ 0) := by
  have hc : M.c ≠ 0 := h.1
  obtain ⟨Xt, hXdef⟩ : ∃ Xt : ℂ → ℂ, Xt = fun z => ((z - l) ^ 2 * (℘[M.L - l] z - 1 / l ^ 2) + 1) / M.c ^ 2 -
      M.ι.symm (M.W.b₂ / 12) * (z - l) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Yt, hYdef⟩ : ∃ Yt : ℂ → ℂ, Yt = fun z => (((z - l) ^ 3 * ℘'[M.L - l] z - 2) / M.c ^ 3 -
      M.ι.symm M.W.a₁ * (z - l) * Xt z - M.ι.symm M.W.a₃ * (z - l) ^ 3) / 2 := ⟨_, rfl⟩
  have hP0 := M.L.analyticAt_weierstrassPExcept l
  have hD0 := M.L.analyticAt_derivWeierstrassPExcept l
  have hXt : AnalyticAt ℂ Xt l := by
    rw [hXdef]
    fun_prop
  have hYt : AnalyticAt ℂ Yt l := by
    rw [hYdef]
    fun_prop
  have hXl : Xt l = 1 / M.c ^ 2 := by
    rw [hXdef]
    beta_reduce
    ring
  have hYl : Yt l = -1 / M.c ^ 3 := by
    rw [hYdef]
    beta_reduce
    ring
  have hYne : Yt l ≠ 0 := by
    rw [hYl]
    exact div_ne_zero (by norm_num) (pow_ne_zero 3 hc)
  have hf : AnalyticAt ℂ (fun z => -Xt z / Yt z) l := hXt.neg.div hYt hYne
  have hg : AnalyticAt ℂ (fun z => -(z - l) ^ 2 / Yt z) l := by
    have hs : AnalyticAt ℂ (fun z => -(z - l) ^ 2) l := by fun_prop
    exact hs.div hYt hYne
  have hfl : -Xt l / Yt l = M.c := by
    rw [hXl, hYl]
    field_simp
  have hev1 : ∀ᶠ z in 𝓝 l, Yt z ≠ 0 := hYt.continuousAt.eventually_ne hYne
  have hev2 : ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice :=
    eventually_nhdsWithin_iff.mp (GlobalTheory.eventually_ne_notMem_periodLattice M.L l)
  refine ⟨fun z => -Xt z / Yt z, fun z => -(z - l) ^ 2 / Yt z, hf, hg, hfl, by simp, ?_⟩
  filter_upwards [hev1, hev2] with z hz1 hz2
  by_cases hzl : z = l
  · rw [hzl]
    exact ⟨by simp [Mdl.u, hl], by simp [Mdl.w, hl], fun h' => absurd rfl h'⟩
  have hzL := hz2 hzl
  have hs : z - l ≠ 0 := sub_ne_zero.mpr hzl
  have hP : ℘[M.L] z = ℘[M.L - l] z - 1 / l ^ 2 + 1 / (z - l) ^ 2 := by
    have e := M.L.weierstrassPExcept_def ⟨l, hl⟩ z
    linear_combination -e
  have hD : ℘'[M.L] z = ℘'[M.L - l] z - 2 / (z - l) ^ 3 := by
    have e := M.L.derivWeierstrassPExcept_def ⟨l, hl⟩ z
    linear_combination -e
  have hx : (z - l) ^ 2 * M.x z = Xt z := by
    rw [hXdef]
    simp only [Mdl.x, hP]
    field_simp
  have hy : (z - l) ^ 3 * M.y z = Yt z := by
    rw [hYdef]
    simp only [Mdl.y, hD]
    rw [← hx]
    field_simp
  have hy0 : M.y z ≠ 0 := by
    intro h0
    apply hz1
    rw [← hy, h0, mul_zero]
  refine ⟨?_, ?_, fun _ => ⟨hzL, hy0⟩⟩
  · simp only [Mdl.u, if_neg hzL]
    rw [← hx, ← hy]
    field_simp
  · simp only [Mdl.w, if_neg hzL]
    rw [← hy]
    field_simp

/- English proof (translation)
Establish `heq` using `congrArg M.ι (equation M h hz)`. Simplify using `only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply] at heq`. Take `⟨-, h1, h2, h3, h4, h6, -, -, -⟩` from `h`. Assume the negation of the conclusion as `hY'`. Establish `hY` using `not_lt.mp hY'`.

Establish `hmax : ∀ (a b : ℂ_[q]) (B : ℝ), ‖a‖ ≤ B → ‖b‖ ≤ B → ‖a + b‖ ≤ B` using `fun a b B ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`. Establish `hX0 : 0 ≤ ‖M.ι (M.x z)‖` using `norm_nonneg _`. Establish `hX2 : ‖M.ι (M.x z)‖ ≤ ‖M.ι (M.x z)‖ ^ 2` using `by nlinarith`. Establish `hX1 : (1 : ℝ) ≤ ‖M.ι (M.x z)‖ ^ 2` using `by nlinarith`. Establish `hL : ‖M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)‖ ≤ ‖M.ι (M.x z)‖ ^ 2`.

Use `hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hY 2`. Rewrite using `[norm_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hR : ‖M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆‖ ≤ ‖M.ι (M.x z)‖ ^ 2`. Use `hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX3 : M.ι (M.x z) ^ 3 = (M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)) + -(M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆)`.

Rewrite using `[heq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcube : ‖M.ι (M.x z)‖ ^ 3 ≤ ‖M.ι (M.x z)‖ ^ 2`. Rewrite using `[← norm_pow, hX3]`. Conclude with `hmax _ _ _ hL (by rw [norm_neg]; exact hR)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_x_lt (h : M.Ok) {z : ℂ} (hz : z ∉ M.L.lattice) (hx : 1 < ‖M.ι (M.x z)‖) :
    ‖M.ι (M.x z)‖ < ‖M.ι (M.y z)‖ := by
  have heq := congrArg M.ι (equation M h hz)
  simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply] at heq
  obtain ⟨-, h1, h2, h3, h4, h6, -, -, -⟩ := h
  by_contra hY'
  have hY := not_lt.mp hY'
  have hmax : ∀ (a b : ℂ_[q]) (B : ℝ), ‖a‖ ≤ B → ‖b‖ ≤ B → ‖a + b‖ ≤ B := fun a b B ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hX0 : 0 ≤ ‖M.ι (M.x z)‖ := norm_nonneg _
  have hX2 : ‖M.ι (M.x z)‖ ≤ ‖M.ι (M.x z)‖ ^ 2 := by nlinarith
  have hX1 : (1 : ℝ) ≤ ‖M.ι (M.x z)‖ ^ 2 := by nlinarith
  have hL : ‖M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)‖ ≤
      ‖M.ι (M.x z)‖ ^ 2 := by
    refine hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_
    · rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hY 2
    · rw [norm_mul, norm_mul]
      calc ‖M.W.a₁‖ * ‖M.ι (M.x z)‖ * ‖M.ι (M.y z)‖ ≤ 1 * ‖M.ι (M.x z)‖ * ‖M.ι (M.x z)‖ := by gcongr
        _ = ‖M.ι (M.x z)‖ ^ 2 := by ring
    · rw [norm_mul]
      calc ‖M.W.a₃‖ * ‖M.ι (M.y z)‖ ≤ 1 * ‖M.ι (M.x z)‖ := by gcongr
        _ ≤ ‖M.ι (M.x z)‖ ^ 2 := by linarith
  have hR : ‖M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆‖ ≤ ‖M.ι (M.x z)‖ ^ 2 := by
    refine hmax _ _ _ (hmax _ _ _ ?_ ?_) ?_
    · rw [norm_mul, norm_pow]
      calc ‖M.W.a₂‖ * ‖M.ι (M.x z)‖ ^ 2 ≤ 1 * ‖M.ι (M.x z)‖ ^ 2 := by gcongr
        _ = ‖M.ι (M.x z)‖ ^ 2 := by ring
    · rw [norm_mul]
      calc ‖M.W.a₄‖ * ‖M.ι (M.x z)‖ ≤ 1 * ‖M.ι (M.x z)‖ := by gcongr
        _ ≤ ‖M.ι (M.x z)‖ ^ 2 := by linarith
    · linarith
  have hX3 : M.ι (M.x z) ^ 3 = (M.ι (M.y z) ^ 2 + M.W.a₁ * M.ι (M.x z) * M.ι (M.y z) + M.W.a₃ * M.ι (M.y z)) +
      -(M.W.a₂ * M.ι (M.x z) ^ 2 + M.W.a₄ * M.ι (M.x z) + M.W.a₆) := by
    rw [heq]
    ring
  have hcube : ‖M.ι (M.x z)‖ ^ 3 ≤ ‖M.ι (M.x z)‖ ^ 2 := by
    rw [← norm_pow, hX3]
    exact hmax _ _ _ hL (by rw [norm_neg]; exact hR)
  nlinarith

end GlobalTheory.MomOne.UW

namespace GlobalTheory.MomOne
open UW

/- English proof (translation)
Introduce `q _ M h`. Establish `h0 : (0 : ℂ) ∈ M.L.lattice` using `zero_mem _`. Establish `hlat : ∀ l ∈ M.L.lattice, AnalyticAt ℂ M.u l ∧ AnalyticAt ℂ M.w l ∧ deriv M.u l = M.c ∧ deriv M.w l = 0 ∧ ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice ∧ M.y z ≠ 0`. Introduce `l hl`. Take `⟨f, g, hf, hg, hfl, hgl, hev⟩` from `UW.exists_analytic_u_w_factor_near_lattice M h hl`.

Establish `hu : M.u =ᶠ[𝓝 l] fun z => (z - l) * f z` using `hev.mono fun z hz => hz.1`. Establish `hw : M.w =ᶠ[𝓝 l] fun z => (z - l) * g z` using `hev.mono fun z hz => hz.2.1`. Establish `hdu : HasDerivAt (fun z => (z - l) * f z) (1 * f l + (l - l) * deriv f l) l` using `((hasDerivAt_id' l).sub_const l).mul hf.differentiableAt.hasDerivAt`. Establish `hdw : HasDerivAt (fun z => (z - l) * g z) (1 * g l + (l - l) * deriv g l) l` using `((hasDerivAt_id' l).sub_const l).mul hg.differentiableAt.hasDerivAt`. Establish `hfa : AnalyticAt ℂ (fun z => (z - l) * f z) l` using `by fun_prop`.

Establish `hga : AnalyticAt ℂ (fun z => (z - l) * g z) l` using `by fun_prop`. Use `⟨hfa.congr hu.symm, hga.congr hw.symm, ?_, ?_, hev.mono fun z hz => hz.2.2⟩` and prove the remaining obligations. Rewrite using `[hu.deriv_eq, hdu.deriv]`. Simplify using `[hfl]`. Rewrite using `[hw.deriv_eq, hdw.deriv]`.

Simplify using `[hgl]`. Use `⟨UW.ell_u M, UW.ell_w M, ⟨UW.meromorphic_x M, fun l hl z => UW.x_add M hl z⟩, ⟨UW.meromorphic_y M, fun l hl z => UW.y_add M hl z⟩, by simp [Mdl.u, h0], by simp [Mdl.w, h0], (hlat 0 h0).2.2.1, fun z hz => ⟨UW.analyticAt_x_of_not_mem_lattice M hz, UW.analyticAt_y M hz⟩, ?_⟩` and prove the remaining obligations. Introduce `z₀ hs`. Distinguish the cases in `hl : z₀ ∈ M.L.lattice`. Take `⟨hua, hwa, hdu, hdw, hev⟩` from `hlat z₀ hl`.

Establish `hu0 : M.u z₀ = 0` using `by simp [Mdl.u, hl]`. Establish `hw0 : M.w z₀ = 0` using `by simp [Mdl.w, hl]`. Use `⟨hua, hwa, by simp [hu0], by simp [hw0], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eventually_nhdsWithin_iff] filter_upwards [hev] with z hz hne`. Take `⟨hzL, hy⟩` from `hz hne`.

Establish `hu : M.u z = -M.x z / M.y z` using `by simp [Mdl.u, hzL]`. Establish `hw : M.w z = -1 / M.y z` using `by simp [Mdl.w, hzL]`. Use `⟨hzL, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hw]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts. Use `filter_upwards [hev] with z hz`. Distinguish the cases in `hne : z = z₀`. Rewrite using `[hne]`.

Simplify using `[hu0, hw0, hdu, hdw]`. Take `⟨hzL, hy⟩` from `hz hne`. Conclude with `UW.flow_off M h hzL hy`. Establish `hx1 : 1 < ‖M.ι (M.x z₀)‖` using `hs.resolve_left hl`. Establish `hlt` using `UW.norm_x_lt M h hl hx1`.

Establish `hYpos : 0 < ‖M.ι (M.y z₀)‖` using `lt_trans (lt_trans zero_lt_one hx1) hlt`. Establish `hy : M.y z₀ ≠ 0` using `fun h0 => by simp [h0] at hYpos`. Take `⟨hua, hwa⟩` from `UW.analyticAt_uw M hl hy`. Establish `hu0 : M.u z₀ = -M.x z₀ / M.y z₀` using `by simp [Mdl.u, hl]`. Establish `hw0 : M.w z₀ = -1 / M.y z₀` using `by simp [Mdl.w, hl]`.

Establish `hev1` using `GlobalTheory.eventually_notMem_periodLattice M.L hl`. Establish `hev2` using `(UW.analyticAt_y M hl).continuousAt.eventually_ne hy`. Use `⟨hua, hwa, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu0, map_div₀, map_neg, norm_div, norm_neg, div_lt_one hYpos]`. Conclude with `hlt`.

Rewrite using `[hw0, map_div₀, map_neg, map_one, norm_div, norm_neg, norm_one, div_lt_one hYpos]`. Conclude with `lt_trans hx1 hlt`. Use `filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2] with z hzL hyz`. Establish `hu : M.u z = -M.x z / M.y z` using `by simp [Mdl.u, hzL]`. Establish `hw : M.w z = -1 / M.y z` using `by simp [Mdl.w, hzL]`.

Use `⟨hzL, hyz, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts.

Use `filter_upwards [hev1, hev2] with z hzL hyz`. Conclude with `UW.flow_off M h hzL hyz`.
-/
theorem uw_elliptic_flow : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q), M.Ok → Ell M.L M.u ∧ Ell M.L M.w ∧ Ell M.L M.x ∧ Ell M.L M.y ∧ M.u 0 = 0 ∧ M.w 0 = 0 ∧ deriv M.u 0 = M.c ∧ (∀ z, z ∉ M.L.lattice → AnalyticAt ℂ M.x z ∧ AnalyticAt ℂ M.y z) ∧ ∀ z₀, M.Small z₀ → AnalyticAt ℂ M.u z₀ ∧ AnalyticAt ℂ M.w z₀ ∧ ‖M.ι (M.u z₀)‖ < 1 ∧ ‖M.ι (M.w z₀)‖ < 1 ∧ (∀ᶠ z in 𝓝[≠] z₀, z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) ∧ ∀ᶠ z in 𝓝 z₀, (let a₁ := M.ι.symm M.W.a₁; let a₂ := M.ι.symm M.W.a₂; let a₃ := M.ι.symm M.W.a₃; let a₄ := M.ι.symm M.W.a₄; let a₆ := M.ι.symm M.W.a₆; let u := M.u z; let w := M.w z; w = u ^ 3 + a₁ * u * w + a₂ * u ^ 2 * w + a₃ * w ^ 2 + a₄ * u * w ^ 2 + a₆ * w ^ 3 ∧ deriv M.u z = M.c * (1 - a₁ * u - a₂ * u ^ 2 - 2 * a₃ * w - 2 * a₄ * u * w - 3 * a₆ * w ^ 2) ∧ deriv M.w z = M.c * (3 * u ^ 2 + a₁ * w + 2 * a₂ * u * w + a₄ * w ^ 2)) := by
  intro q _ M h
  have h0 : (0 : ℂ) ∈ M.L.lattice := zero_mem _
  have hlat : ∀ l ∈ M.L.lattice, AnalyticAt ℂ M.u l ∧ AnalyticAt ℂ M.w l ∧ deriv M.u l = M.c ∧
      deriv M.w l = 0 ∧ ∀ᶠ z in 𝓝 l, z ≠ l → z ∉ M.L.lattice ∧ M.y z ≠ 0 := by
    intro l hl
    obtain ⟨f, g, hf, hg, hfl, hgl, hev⟩ := UW.exists_analytic_u_w_factor_near_lattice M h hl
    have hu : M.u =ᶠ[𝓝 l] fun z => (z - l) * f z := hev.mono fun z hz => hz.1
    have hw : M.w =ᶠ[𝓝 l] fun z => (z - l) * g z := hev.mono fun z hz => hz.2.1
    have hdu : HasDerivAt (fun z => (z - l) * f z) (1 * f l + (l - l) * deriv f l) l :=
      ((hasDerivAt_id' l).sub_const l).mul hf.differentiableAt.hasDerivAt
    have hdw : HasDerivAt (fun z => (z - l) * g z) (1 * g l + (l - l) * deriv g l) l :=
      ((hasDerivAt_id' l).sub_const l).mul hg.differentiableAt.hasDerivAt
    have hfa : AnalyticAt ℂ (fun z => (z - l) * f z) l := by fun_prop
    have hga : AnalyticAt ℂ (fun z => (z - l) * g z) l := by fun_prop
    refine ⟨hfa.congr hu.symm, hga.congr hw.symm, ?_, ?_, hev.mono fun z hz => hz.2.2⟩
    · rw [hu.deriv_eq, hdu.deriv]
      simp [hfl]
    · rw [hw.deriv_eq, hdw.deriv]
      simp [hgl]
  refine ⟨UW.ell_u M, UW.ell_w M, ⟨UW.meromorphic_x M, fun l hl z => UW.x_add M hl z⟩,
    ⟨UW.meromorphic_y M, fun l hl z => UW.y_add M hl z⟩, by simp [Mdl.u, h0], by simp [Mdl.w, h0],
    (hlat 0 h0).2.2.1, fun z hz => ⟨UW.analyticAt_x_of_not_mem_lattice M hz, UW.analyticAt_y M hz⟩, ?_⟩
  intro z₀ hs
  by_cases hl : z₀ ∈ M.L.lattice
  · obtain ⟨hua, hwa, hdu, hdw, hev⟩ := hlat z₀ hl
    have hu0 : M.u z₀ = 0 := by simp [Mdl.u, hl]
    have hw0 : M.w z₀ = 0 := by simp [Mdl.w, hl]
    refine ⟨hua, hwa, by simp [hu0], by simp [hw0], ?_, ?_⟩
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [hev] with z hz hne
      obtain ⟨hzL, hy⟩ := hz hne
      have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hzL]
      have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hzL]
      refine ⟨hzL, hy, ?_, ?_⟩
      · rw [hu, hw]
        ring
      · rw [hw]
        field_simp
    · filter_upwards [hev] with z hz
      by_cases hne : z = z₀
      · rw [hne]
        simp [hu0, hw0, hdu, hdw]
      · obtain ⟨hzL, hy⟩ := hz hne
        exact UW.flow_off M h hzL hy
  · have hx1 : 1 < ‖M.ι (M.x z₀)‖ := hs.resolve_left hl
    have hlt := UW.norm_x_lt M h hl hx1
    have hYpos : 0 < ‖M.ι (M.y z₀)‖ := lt_trans (lt_trans zero_lt_one hx1) hlt
    have hy : M.y z₀ ≠ 0 := fun h0 => by simp [h0] at hYpos
    obtain ⟨hua, hwa⟩ := UW.analyticAt_uw M hl hy
    have hu0 : M.u z₀ = -M.x z₀ / M.y z₀ := by simp [Mdl.u, hl]
    have hw0 : M.w z₀ = -1 / M.y z₀ := by simp [Mdl.w, hl]
    have hev1 := GlobalTheory.eventually_notMem_periodLattice M.L hl
    have hev2 := (UW.analyticAt_y M hl).continuousAt.eventually_ne hy
    refine ⟨hua, hwa, ?_, ?_, ?_, ?_⟩
    · rw [hu0, map_div₀, map_neg, norm_div, norm_neg, div_lt_one hYpos]
      exact hlt
    · rw [hw0, map_div₀, map_neg, map_one, norm_div, norm_neg, norm_one, div_lt_one hYpos]
      exact lt_trans hx1 hlt
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2] with z hzL hyz
      have hu : M.u z = -M.x z / M.y z := by simp [Mdl.u, hzL]
      have hw : M.w z = -1 / M.y z := by simp [Mdl.w, hzL]
      refine ⟨hzL, hyz, ?_, ?_⟩
      · rw [hu, hw]
        ring
      · rw [hw]
        field_simp
    · filter_upwards [hev1, hev2] with z hzL hyz
      exact UW.flow_off M h hzL hyz

end GlobalTheory.MomOne
