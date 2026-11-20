import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpLift

section Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/- English proof (translation)
Introduce `z hz`. Establish `h0mem : (0 : E) ∈ ball (0 : E) (r / 2)` using `mem_ball_self (by linarith)`. Establish `hk0 : k 0 = 0`. Establish `h00` using `ha 0 h0mem 0 h0mem`. Rewrite `h00` using `[add_zero]`.

Establish `h00' : k 0 + k 0 = k 0 + 0` using `by rw [add_zero]; exact h00.symm`. Conclude with `add_left_cancel h00'`. Establish `hmul : ∀ N : ℕ, 0 < N → k z = (N : ℂ) • k ((N : ℂ)⁻¹ • z)`. Introduce `N hN`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`.

Establish `hnorm : ∀ n : ℕ, n ≤ N → (n : ℂ) • ((N : ℂ)⁻¹ • z) ∈ ball (0 : E) (r / 2)`. Introduce `n hn`. Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[smul_smul, norm_smul]`. Establish `hle : ‖(n : ℂ) * (N : ℂ)⁻¹‖ ≤ 1`.

Rewrite using `[norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast, mul_inv_le_iff₀ (by exact_mod_cast hN), _root_.one_mul]`. Conclude with `hn` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2)`. Establish `h1'` using `hnorm 1 hN`.

Rewrite `h1'` using `[Nat.cast_one, one_smul]`. Then use the resulting hypothesis. Establish `hind : ∀ n : ℕ, n ≤ N → k ((n : ℂ) • ((N : ℂ)⁻¹ • z)) = (n : ℂ) • k ((N : ℂ)⁻¹ • z)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _`.

Simplify using `[hk0]`. Consider the case `succ n ih`. Introduce `hn`. Rewrite using `[Nat.cast_succ, add_smul, one_smul, ha _ (hnorm n (Nat.le_of_succ_le hn)) _ h1, ih (Nat.le_of_succ_le hn), add_smul, one_smul]`. Establish `hN'` using `hind N le_rfl`.

Rewrite `hN'` using `[smul_smul, mul_inv_cancel₀ hNc, one_smul]`. Then use the resulting hypothesis. Establish `hdiff : DifferentiableAt ℂ k 0` using `hd.differentiableAt (ball_mem_nhds 0 hr)`. Establish `hlim` using `hdiff.hasFDerivAt.lim z (c := fun n : ℕ => (n : ℂ)) (l := atTop) (by`. Simplify using `only [Complex.norm_natCast]`. Conclude with `tendsto_natCast_atTop_atTop)`.

Establish `hev : (fun n : ℕ => (n : ℂ) • (k (0 + ((n : ℂ))⁻¹ • z) - k 0)) =ᶠ[atTop] fun _ => k z` using `by filter_upwards [eventually_gt_atTop 0] with N hN`. Rewrite using `[zero_add, hk0, sub_zero, ← hmul N hN]`. Conclude with `tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim`.
-/
theorem eq_fderiv_of_locally_additive {k : E → F} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ k (ball 0 r))
    (ha : ∀ z ∈ ball (0 : E) (r / 2), ∀ w ∈ ball (0 : E) (r / 2), k (z + w) = k z + k w) :
    ∀ z ∈ ball (0 : E) (r / 2), k z = fderiv ℂ k 0 z := by
  intro z hz
  have h0mem : (0 : E) ∈ ball (0 : E) (r / 2) := mem_ball_self (by linarith)
  have hk0 : k 0 = 0 := by
    have h00 := ha 0 h0mem 0 h0mem
    rw [add_zero] at h00
    have h00' : k 0 + k 0 = k 0 + 0 := by rw [add_zero]; exact h00.symm
    exact add_left_cancel h00'
  have hmul : ∀ N : ℕ, 0 < N → k z = (N : ℂ) • k ((N : ℂ)⁻¹ • z) := by
    intro N hN
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hnorm : ∀ n : ℕ, n ≤ N → (n : ℂ) • ((N : ℂ)⁻¹ • z) ∈ ball (0 : E) (r / 2) := by
      intro n hn
      rw [mem_ball_zero_iff] at hz ⊢
      rw [smul_smul, norm_smul]
      have hle : ‖(n : ℂ) * (N : ℂ)⁻¹‖ ≤ 1 := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
          mul_inv_le_iff₀ (by exact_mod_cast hN), _root_.one_mul]
        exact_mod_cast hn
      calc ‖(n : ℂ) * (N : ℂ)⁻¹‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ < r / 2 := by rwa [_root_.one_mul]
    have h1 : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2) := by
      have h1' := hnorm 1 hN
      rwa [Nat.cast_one, one_smul] at h1'
    have hind : ∀ n : ℕ, n ≤ N → k ((n : ℂ) • ((N : ℂ)⁻¹ • z)) = (n : ℂ) • k ((N : ℂ)⁻¹ • z) := by
      intro n
      induction n with
      | zero => intro _; simp [hk0]
      | succ n ih =>
        intro hn
        rw [Nat.cast_succ, add_smul, one_smul, ha _ (hnorm n (Nat.le_of_succ_le hn)) _ h1,
          ih (Nat.le_of_succ_le hn), add_smul, one_smul]
    have hN' := hind N le_rfl
    rwa [smul_smul, mul_inv_cancel₀ hNc, one_smul] at hN'
  have hdiff : DifferentiableAt ℂ k 0 := hd.differentiableAt (ball_mem_nhds 0 hr)
  have hlim := hdiff.hasFDerivAt.lim z (c := fun n : ℕ => (n : ℂ)) (l := atTop) (by
    simp only [Complex.norm_natCast]
    exact tendsto_natCast_atTop_atTop)
  have hev : (fun n : ℕ => (n : ℂ) • (k (0 + ((n : ℂ))⁻¹ • z) - k 0)) =ᶠ[atTop] fun _ => k z := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [zero_add, hk0, sub_zero, ← hmul N hN]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_nat_gt (‖z‖ / ρ)`. Use `⟨N + 1, N.succ_pos, ?_⟩` and prove the remaining obligations. Establish `hpos : (0 : ℝ) < (N : ℝ) + 1` using `by positivity`. Establish `hz : ‖z‖ < N * ρ` using `(div_lt_iff₀ hρ).mp hN`. Rewrite using `[norm_smul, norm_inv, Complex.norm_natCast]`.

Use `push_cast`. Rewrite using `[inv_mul_eq_div, div_lt_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_small_fraction (z : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, 0 < N ∧ ‖((N : ℂ)⁻¹ • z)‖ < ρ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ / ρ)
  refine ⟨N + 1, N.succ_pos, ?_⟩
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hz : ‖z‖ < N * ρ := (div_lt_iff₀ hρ).mp hN
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  push_cast
  rw [inv_mul_eq_div, div_lt_iff₀ hpos]
  nlinarith

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_smul]`.
-/
theorem nsmul_inv_smul (z : E) {N : ℕ} (hN : 0 < N) : N • ((N : ℂ)⁻¹ • z) = z := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_smul]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Rewrite using `[zero_nsmul, pow_zero]`. Establish `h0` using `h 0 0`. Rewrite `h0` using `[add_zero]`.

Conclude with `mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)`. Consider the case `succ N ih => rw [succ_nsmul, h, ih, pow_succ]`.
-/
theorem map_nsmul_of_add {V M : Type*} [AddMonoid V] [Group M] (a : V → M)
    (h : ∀ x y, a (x + y) = a x * a y) (x : V) (N : ℕ) : a (N • x) = a x ^ N := by
  induction N with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h0 := h 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  | succ N ih => rw [succ_nsmul, h, ih, pow_succ]

/- English proof (translation)
Establish `ht : Tendsto h (𝓝 0) (𝓝 0)`. Simplify using `using (LinearMap.continuous_of_finiteDimensional h).tendsto 0`. Establish `ht' : Tendsto h' (𝓝 0) (𝓝 0)`. Simplify using `using (LinearMap.continuous_of_finiteDimensional h').tendsto 0`. Establish `hU` using `(ht.eventually_mem (ball_mem_nhds (0 : F) hr)).and (ht'.eventually_mem (ball_mem_nhds (0 : F) hr))`.

Take `⟨δ, hδ, hδU⟩` from `Metric.eventually_nhds_iff.mp hU`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨N, hNpos, hN⟩` from `exists_small_fraction z hδ`. Establish `hNc : (N : ℂ)⁻¹ ≠ 0` using `inv_ne_zero (Nat.cast_ne_zero.mpr hNpos.ne')`. Establish `hm` using `hδU (show dist ((N : ℂ)⁻¹ • z) 0 < δ by rwa [dist_zero_right])`.

Establish `heq` using `hinj _ hm.1 _ hm.2 (H _)`. Rewrite `heq` using `[map_smul, map_smul]`. Conclude with `smul_right_injective F hNc heq`.
-/
theorem linear_unique {M : Type*} [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (ex : F → M) {r : ℝ} (hr : 0 < r)
    (hinj : ∀ w ∈ ball (0 : F) r, ∀ w' ∈ ball (0 : F) r, ex w = ex w' → w = w')
    (h h' : E →ₗ[ℂ] F) (H : ∀ z, ex (h z) = ex (h' z)) : h = h' := by
  have ht : Tendsto h (𝓝 0) (𝓝 0) := by
    simpa using (LinearMap.continuous_of_finiteDimensional h).tendsto 0
  have ht' : Tendsto h' (𝓝 0) (𝓝 0) := by
    simpa using (LinearMap.continuous_of_finiteDimensional h').tendsto 0
  have hU := (ht.eventually_mem (ball_mem_nhds (0 : F) hr)).and
    (ht'.eventually_mem (ball_mem_nhds (0 : F) hr))
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.mp hU
  refine LinearMap.ext fun z => ?_
  obtain ⟨N, hNpos, hN⟩ := exists_small_fraction z hδ
  have hNc : (N : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hNpos.ne')
  have hm := hδU (show dist ((N : ℂ)⁻¹ • z) 0 < δ by rwa [dist_zero_right])
  have heq := hinj _ hm.1 _ hm.2 (H _)
  rw [map_smul, map_smul] at heq
  exact smul_right_injective F hNc heq

/- English proof (translation)
Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.mp h`. Take `⟨r, hr, hrv⟩` from `Metric.mem_nhds_iff.mp hv`. Conclude with `⟨interior u, isOpen_interior, mem_interior_iff_mem_nhds.mpr hu, r, hr, fun b hb z hz => huv ⟨interior_subset hb, hrv hz⟩⟩`.
-/
theorem box_of_eventually {A : Type*} [TopologicalSpace A] {b₀ : A} {p : A × E → Prop}
    (h : ∀ᶠ bz in 𝓝 (b₀, (0 : E)), p bz) :
    ∃ W : Set A, IsOpen W ∧ b₀ ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ b ∈ W, ∀ z ∈ ball (0 : E) r, p (b, z) := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp h
  obtain ⟨r, hr, hrv⟩ := Metric.mem_nhds_iff.mp hv
  exact ⟨interior u, isOpen_interior, mem_interior_iff_mem_nhds.mpr hu, r, hr,
    fun b hb z hz => huv ⟨interior_subset hb, hrv hz⟩⟩

end Analysis

/- English proof (translation)
Establish `hr2 : 0 < r / 2` using `by linarith`. Establish `hsub : ∀ z ∈ ball (0 : E) (r / 2), z ∈ ball (0 : E) r` using `fun z hz => ball_subset_ball (by linarith) hz`. Establish `hdz : ∀ b ∈ W, DifferentiableOn ℂ (fun z => k (b, z)) (ball (0 : E) r)`. Introduce `b hb z hz`. Conclude with `((hk b hb z hz).1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)).differentiableWithinAt`.

Establish `hadd : ∀ b ∈ W, ∀ z ∈ ball (0 : E) (r / 2), ∀ w ∈ ball (0 : E) (r / 2), k (b, z + w) = k (b, z) + k (b, w)`. Introduce `b hb z hz w hw`. Establish `hzw : z + w ∈ ball (0 : E) r`. Rewrite `hz`, `hw`, the goal using `[mem_ball_zero_iff]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨-, hu1, hb1⟩` from `hk b hb (z + w) hzw`. Take `⟨-, hu2, hb2⟩` from `hk b hb z (hsub z hz)`. Take `⟨-, hu3, hb3⟩` from `hk b hb w (hsub w hw)`. Use `hinj b hb _ (ball_subset_ball (by linarith) hb1) _ ?_ ?_` and prove the remaining obligations. Rewrite `hb2`, `hb3`, the goal using `[mem_ball_zero_iff]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hex b hb, ← hu1, ← hu2, ← hu3, hu b hb]`. Establish `hkfd : ∀ b ∈ W, ∀ z ∈ ball (0 : E) (r / 2), k (b, z) = fderiv ℂ (fun z => k (b, z)) 0 z` using `fun b hb => eq_fderiv_of_locally_additive (k := fun z => k (b, z)) hr (hdz b hb) (hadd b hb)`. Set `L : A → (E →L[ℂ] F)` to `fun b => fderiv ℂ (fun z => k (b, z)) 0`. Establish `hkey : ∀ b ∈ W, ∀ z : E, ∀ N : ℕ, 0 < N → (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2) → L b z = (N : ℂ) • k (b, (N : ℂ)⁻¹ • z)`.

Introduce `b hb z N hN hz`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_inv_cancel₀ hNc, one_smul]`. Use `_ = (N : ℂ) • L b ((N : ℂ)⁻¹ • z) := map_smul _ _ _`.

Use `_ = (N : ℂ) • k (b, (N : ℂ)⁻¹ • z) := by rw [hkfd b hb _ hz]`. Use `⟨fun b => (L b : E →ₗ[ℂ] F), ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb z`. Take `⟨N, hN, hNz⟩` from `exists_small_fraction z hr2`. Establish `hz' : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2)` using `mem_ball_zero_iff.mpr hNz`.

Take `⟨-, hue, -⟩` from `hk b hb _ (hsub _ hz')`. Use `show ex b (L b z) = u b z`. Rewrite using `[hkey b hb z N hN hz', Nat.cast_smul_eq_nsmul ℂ, map_nsmul_of_add (ex b) (hex b hb), ← hue, ← map_nsmul_of_add (u b) (hu b hb), nsmul_inv_smul z hN]`. Introduce `z`. Take `⟨N, hN, hNz⟩` from `exists_small_fraction z hr2`.

Establish `hz' : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2)` using `mem_ball_zero_iff.mpr hNz`. Establish `hD : DifferentiableOn ℂ (fun b => (N : ℂ) • k (b, (N : ℂ)⁻¹ • z)) W`. Introduce `b hb`. Conclude with `(((hk b hb _ (hsub _ hz')).1.comp b (differentiableAt_id.prodMk (differentiableAt_const _))).const_smul (N : ℂ)).differentiableWithinAt`. Use `hD.congr fun b hb => ?_` and prove the remaining obligations.

Use `show L b z = _`. Conclude with `hkey b hb z N hN hz'`.
-/
theorem lift_of_local {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {P : A → Type*} [∀ b, Group (P b)]
    (ex : ∀ b, F → P b) (u : ∀ b, E → P b) (k : A × E → F) {W : Set A} (hW : IsOpen W) {r r₀ : ℝ}
    (hr : 0 < r) (hr₀ : 0 < r₀)
    (hex : ∀ b ∈ W, ∀ z w, ex b (z + w) = ex b z * ex b w)
    (hu : ∀ b ∈ W, ∀ z w, u b (z + w) = u b z * u b w)
    (hinj : ∀ b ∈ W, ∀ w ∈ ball (0 : F) r₀, ∀ w' ∈ ball (0 : F) r₀, ex b w = ex b w' → w = w')
    (hk : ∀ b ∈ W, ∀ z ∈ ball (0 : E) r,
      DifferentiableAt ℂ k (b, z) ∧ u b z = ex b (k (b, z)) ∧ k (b, z) ∈ ball (0 : F) (r₀ / 2)) :
    ∃ hl : A → (E →ₗ[ℂ] F), (∀ b ∈ W, ∀ z, ex b (hl b z) = u b z) ∧
      ∀ z, DifferentiableOn ℂ (fun b => hl b z) W := by
  have hr2 : 0 < r / 2 := by linarith
  have hsub : ∀ z ∈ ball (0 : E) (r / 2), z ∈ ball (0 : E) r :=
    fun z hz => ball_subset_ball (by linarith) hz
  have hdz : ∀ b ∈ W, DifferentiableOn ℂ (fun z => k (b, z)) (ball (0 : E) r) := by
    intro b hb z hz
    exact ((hk b hb z hz).1.comp z
      ((differentiableAt_const b).prodMk differentiableAt_id)).differentiableWithinAt
  have hadd : ∀ b ∈ W, ∀ z ∈ ball (0 : E) (r / 2), ∀ w ∈ ball (0 : E) (r / 2),
      k (b, z + w) = k (b, z) + k (b, w) := by
    intro b hb z hz w hw
    have hzw : z + w ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff] at hz hw ⊢
      calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
        _ < r := by linarith
    obtain ⟨-, hu1, hb1⟩ := hk b hb (z + w) hzw
    obtain ⟨-, hu2, hb2⟩ := hk b hb z (hsub z hz)
    obtain ⟨-, hu3, hb3⟩ := hk b hb w (hsub w hw)
    refine hinj b hb _ (ball_subset_ball (by linarith) hb1) _ ?_ ?_
    · rw [mem_ball_zero_iff] at hb2 hb3 ⊢
      calc ‖k (b, z) + k (b, w)‖ ≤ ‖k (b, z)‖ + ‖k (b, w)‖ := norm_add_le _ _
        _ < r₀ := by linarith
    · rw [hex b hb, ← hu1, ← hu2, ← hu3, hu b hb]
  have hkfd : ∀ b ∈ W, ∀ z ∈ ball (0 : E) (r / 2), k (b, z) = fderiv ℂ (fun z => k (b, z)) 0 z :=
    fun b hb => eq_fderiv_of_locally_additive (k := fun z => k (b, z)) hr (hdz b hb) (hadd b hb)
  let L : A → (E →L[ℂ] F) := fun b => fderiv ℂ (fun z => k (b, z)) 0
  have hkey : ∀ b ∈ W, ∀ z : E, ∀ N : ℕ, 0 < N → (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2) →
      L b z = (N : ℂ) • k (b, (N : ℂ)⁻¹ • z) := by
    intro b hb z N hN hz
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    calc L b z = L b ((N : ℂ) • ((N : ℂ)⁻¹ • z)) := by
          rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
      _ = (N : ℂ) • L b ((N : ℂ)⁻¹ • z) := map_smul _ _ _
      _ = (N : ℂ) • k (b, (N : ℂ)⁻¹ • z) := by rw [hkfd b hb _ hz]
  refine ⟨fun b => (L b : E →ₗ[ℂ] F), ?_, ?_⟩
  · intro b hb z
    obtain ⟨N, hN, hNz⟩ := exists_small_fraction z hr2
    have hz' : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2) := mem_ball_zero_iff.mpr hNz
    obtain ⟨-, hue, -⟩ := hk b hb _ (hsub _ hz')
    show ex b (L b z) = u b z
    rw [hkey b hb z N hN hz', Nat.cast_smul_eq_nsmul ℂ, map_nsmul_of_add (ex b) (hex b hb), ← hue,
      ← map_nsmul_of_add (u b) (hu b hb), nsmul_inv_smul z hN]
  · intro z
    obtain ⟨N, hN, hNz⟩ := exists_small_fraction z hr2
    have hz' : (N : ℂ)⁻¹ • z ∈ ball (0 : E) (r / 2) := mem_ball_zero_iff.mpr hNz
    have hD : DifferentiableOn ℂ (fun b => (N : ℂ) • k (b, (N : ℂ)⁻¹ • z)) W := by
      intro b hb
      exact (((hk b hb _ (hsub _ hz')).1.comp b
        (differentiableAt_id.prodMk (differentiableAt_const _))).const_smul (N : ℂ)).differentiableWithinAt
    refine hD.congr fun b hb => ?_
    show L b z = _
    exact hkey b hb z N hN hz'

section Scheme

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

/- English proof (translation)
Establish `h` using `e.add b hb 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)`.
-/
theorem ex_zero (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b 0 = 1 := by
  have h := e.add b hb 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

/- English proof (translation)
Take `⟨V, N, f, L, -, -, hL, -⟩` from `e.log b₀ hb₀`. Take `⟨W, hW, hb₀W, r, hr, hWr⟩` from `box_of_eventually hL`. Use `⟨W, hW, hb₀W, r, hr, fun b hb w hw w' hw' hww' => ?_⟩` and prove the remaining obligations. Establish `h1 : L (b, fun j => valAt' (e.ex b w).left V (f j)) = w` using `hWr b hb w hw`. Establish `h2 : L (b, fun j => valAt' (e.ex b w').left V (f j)) = w'` using `hWr b hb w' hw'`.

Rewrite using `[← h1, ← h2, hww']`.
-/
theorem ex_inj_near (e : FamExp G M B ψ) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ b₀ ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ b ∈ W, ∀ w ∈ ball (0 : Fin g → ℂ) r,
      ∀ w' ∈ ball (0 : Fin g → ℂ) r, e.ex b w = e.ex b w' → w = w' := by
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b₀ hb₀
  obtain ⟨W, hW, hb₀W, r, hr, hWr⟩ := box_of_eventually hL
  refine ⟨W, hW, hb₀W, r, hr, fun b hb w hw w' hw' hww' => ?_⟩
  have h1 : L (b, fun j => valAt' (e.ex b w).left V (f j)) = w := hWr b hb w hw
  have h2 : L (b, fun j => valAt' (e.ex b w').left V (f j)) = w' := hWr b hb w' hw'
  rw [← h1, ← h2, hww']

/- English proof (translation)
Take `⟨hS, hD⟩` from `e.hol U f`. Establish `hmem : (b, (0 : Fin g → ℂ)) ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex b 0).left ⁻¹ᵁ U` using `⟨⟨hb, Set.mem_univ _⟩, h⟩`. Establish `hDa` using `(hD _ hmem).differentiableAt (hS.mem_nhds hmem)`. Conclude with `hDa.comp (0 : Fin g → ℂ) ((differentiableAt_const b).prodMk differentiableAt_id)`.
-/
theorem ex_differentiableAt (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (U : G.left.Opens)
    (f : Γ(G.left, U)) (h : ⊤ ≤ (e.ex b 0).left ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun z => valAt' (e.ex b z).left U f) 0 := by
  obtain ⟨hS, hD⟩ := e.hol U f
  have hmem : (b, (0 : Fin g → ℂ)) ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex b 0).left ⁻¹ᵁ U :=
    ⟨⟨hb, Set.mem_univ _⟩, h⟩
  have hDa := (hD _ hmem).differentiableAt (hS.mem_nhds hmem)
  exact hDa.comp (0 : Fin g → ℂ) ((differentiableAt_const b).prodMk differentiableAt_id)

/- English proof (translation)
Take `⟨V, N, f, L, hV, hLan, hL3, hL4⟩` from `e.log b₀ (hsub hb₀)`. Establish `hu0 : u b₀ 0 = 1`. Establish `h0` using `hu b₀ hb₀ 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)`.

Establish `hue : u b₀ 0 = e.ex b₀ 0` using `by rw [hu0, ex_zero e (hsub hb₀)]`. Establish `hV' : ⊤ ≤ (u b₀ 0).left ⁻¹ᵁ V` using `by rw [hue]; exact hV`. Set `Φ : (Fin n → ℂ) × (Fin m → ℂ) → (Fin n → ℂ) × (Fin N → ℂ)` to `fun bz => (bz.1, fun j => valAt' (u bz.1 bz.2).left V (f j))`. Establish `hΦd : ∀ bz : (Fin n → ℂ) × (Fin m → ℂ), bz ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u bz.1 bz.2).left ⁻¹ᵁ V → DifferentiableAt ℂ Φ bz`. Introduce `bz hbz`.

Use `differentiableAt_fst.prodMk (differentiableAt_pi.mpr fun j => ?_)` and prove the remaining obligations. Conclude with `((hhol V (f j)).2 bz hbz).differentiableAt ((hhol V (f j)).1.mem_nhds hbz)`. Establish `hmem : (b₀, (0 : Fin m → ℂ)) ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u b₀ 0).left ⁻¹ᵁ V` using `⟨⟨hb₀, Set.mem_univ _⟩, hV'⟩`. Establish `hSn : ∀ᶠ bz in 𝓝 (b₀, (0 : Fin m → ℂ)), bz ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u bz.1 bz.2).left ⁻¹ᵁ V` using `(hhol V 0).1.mem_nhds hmem`. Establish `hΦt : Tendsto Φ (𝓝 (b₀, 0)) (𝓝 (Φ (b₀, 0)))` using `(hΦd _ hmem).continuousAt`.

Establish `hΦ0 : Φ (b₀, 0) = (b₀, fun j => valAt' (e.ex b₀ 0).left V (f j))` using `by show (b₀, fun j => valAt' (u b₀ 0).left V (f j)) = _`. Rewrite using `[hue]`. Establish `hLd : ∀ᶠ p in 𝓝 (Φ (b₀, 0)), DifferentiableAt ℂ L p`. Rewrite using `[hΦ0]`. Conclude with `hLan.eventually_analyticAt.mono fun p hp => hp.differentiableAt`.

Rewrite `hL4` using `[← hΦ0]`. Use `⟨fun bz => L (Φ bz), ?_, ?_⟩` and prove the remaining obligations. Use `show L (Φ (b₀, 0)) = 0`. Rewrite using `[hΦ0]`. Conclude with `hL3.self_of_nhds`.

Use `filter_upwards [hSn, hΦt.eventually hL4, hΦt.eventually hLd] with bz hbz h4 hd`. Conclude with `⟨hd.comp bz (hΦd bz hbz), h4 (u bz.1 bz.2) hbz.2 (fun j => rfl), hbz.1.1⟩`.
-/
theorem exists_local_log (e : FamExp G M B ψ) {m : ℕ} {B' : Set (Fin n → ℂ)}
    (u : ∀ b : Fin n → ℂ, (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)) (hsub : B' ⊆ B)
    (hu : ∀ b ∈ B', ∀ z w, u b (z + w) = u b z * u b w)
    (hhol : IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin m → ℂ) => (u bz.1 bz.2).left))
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B') :
    ∃ k : (Fin n → ℂ) × (Fin m → ℂ) → (Fin g → ℂ), k (b₀, 0) = 0 ∧
      ∀ᶠ bz in 𝓝 (b₀, (0 : Fin m → ℂ)), DifferentiableAt ℂ k bz ∧ u bz.1 bz.2 = e.ex bz.1 (k bz) ∧ bz.1 ∈ B' := by
  obtain ⟨V, N, f, L, hV, hLan, hL3, hL4⟩ := e.log b₀ (hsub hb₀)
  have hu0 : u b₀ 0 = 1 := by
    have h0 := hu b₀ hb₀ 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have hue : u b₀ 0 = e.ex b₀ 0 := by rw [hu0, ex_zero e (hsub hb₀)]
  have hV' : ⊤ ≤ (u b₀ 0).left ⁻¹ᵁ V := by rw [hue]; exact hV
  let Φ : (Fin n → ℂ) × (Fin m → ℂ) → (Fin n → ℂ) × (Fin N → ℂ) :=
    fun bz => (bz.1, fun j => valAt' (u bz.1 bz.2).left V (f j))
  have hΦd : ∀ bz : (Fin n → ℂ) × (Fin m → ℂ), bz ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u bz.1 bz.2).left ⁻¹ᵁ V →
      DifferentiableAt ℂ Φ bz := by
    intro bz hbz
    refine differentiableAt_fst.prodMk (differentiableAt_pi.mpr fun j => ?_)
    exact ((hhol V (f j)).2 bz hbz).differentiableAt ((hhol V (f j)).1.mem_nhds hbz)
  have hmem : (b₀, (0 : Fin m → ℂ)) ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u b₀ 0).left ⁻¹ᵁ V :=
    ⟨⟨hb₀, Set.mem_univ _⟩, hV'⟩
  have hSn : ∀ᶠ bz in 𝓝 (b₀, (0 : Fin m → ℂ)), bz ∈ B' ×ˢ Set.univ ∧ ⊤ ≤ (u bz.1 bz.2).left ⁻¹ᵁ V :=
    (hhol V 0).1.mem_nhds hmem
  have hΦt : Tendsto Φ (𝓝 (b₀, 0)) (𝓝 (Φ (b₀, 0))) := (hΦd _ hmem).continuousAt
  have hΦ0 : Φ (b₀, 0) = (b₀, fun j => valAt' (e.ex b₀ 0).left V (f j)) := by
    show (b₀, fun j => valAt' (u b₀ 0).left V (f j)) = _
    rw [hue]
  have hLd : ∀ᶠ p in 𝓝 (Φ (b₀, 0)), DifferentiableAt ℂ L p := by
    rw [hΦ0]
    exact hLan.eventually_analyticAt.mono fun p hp => hp.differentiableAt
  rw [← hΦ0] at hL4
  refine ⟨fun bz => L (Φ bz), ?_, ?_⟩
  · show L (Φ (b₀, 0)) = 0
    rw [hΦ0]
    exact hL3.self_of_nhds
  · filter_upwards [hSn, hΦt.eventually hL4, hΦt.eventually hLd] with bz hbz h4 hd
    exact ⟨hd.comp bz (hΦd bz hbz), h4 (u bz.1 bz.2) hbz.2 (fun j => rfl), hbz.1.1⟩

/- English proof (translation)
Take `⟨k, hk0, hev⟩` from `exists_local_log e u hsub hu hhol hb₀`. Take `⟨W₁, hW₁, hb₀W₁, r₀, hr₀, hinj⟩` from `ex_inj_near e (hsub hb₀)`. Establish `hkc : ContinuousAt k (b₀, 0)` using `hev.self_of_nhds.1.continuousAt`. Establish `hsmall : ∀ᶠ bz in 𝓝 (b₀, (0 : Fin m → ℂ)), k bz ∈ ball (0 : Fin g → ℂ) (r₀ / 2)` using `hkc.eventually_mem (by rw [hk0]; exact ball_mem_nhds _ (half_pos hr₀))`. Take `⟨W₂, hW₂, hb₀W₂, r, hr, hbox⟩` from `box_of_eventually (hev.and hsmall)`.

Establish `hWB : ∀ b ∈ W₂, b ∈ B'` using `fun b hb => (hbox b hb 0 (mem_ball_self hr)).1.2.2`. Take `⟨hl, hl1, hl2⟩` from `lift_of_local (P := fun b => Over.mk (spMap (ψ b)) ⟶ G) e.ex u k (hW₁.inter hW₂) hr hr₀ (fun b hb => e.add b (hsub (hWB b hb.2))) (fun b hb => hu b (hWB b hb.2)) (fun b hb => hinj b hb.1) (fun b hb z hz => ⟨(hbox b hb.2 z hz).1.1, (hbox b hb.2 z hz).1.2.1, (hbox b hb.2 z hz).2⟩)`. Conclude with `⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hb₀W₁, hb₀W₂⟩, fun b hb => hWB b hb.2, hl, hl1, hl2⟩`.
-/
theorem exists_local_linear (e : FamExp G M B ψ) {m : ℕ} {B' : Set (Fin n → ℂ)}
    (u : ∀ b : Fin n → ℂ, (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)) (hsub : B' ⊆ B)
    (hu : ∀ b ∈ B', ∀ z w, u b (z + w) = u b z * u b w)
    (hhol : IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin m → ℂ) => (u bz.1 bz.2).left))
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B') :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ b₀ ∈ W ∧ W ⊆ B' ∧
      ∃ hl : (Fin n → ℂ) → ((Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ b ∈ W, ∀ z, e.ex b (hl b z) = u b z) ∧
        ∀ z, DifferentiableOn ℂ (fun b => hl b z) W := by
  obtain ⟨k, hk0, hev⟩ := exists_local_log e u hsub hu hhol hb₀
  obtain ⟨W₁, hW₁, hb₀W₁, r₀, hr₀, hinj⟩ := ex_inj_near e (hsub hb₀)
  have hkc : ContinuousAt k (b₀, 0) := hev.self_of_nhds.1.continuousAt
  have hsmall : ∀ᶠ bz in 𝓝 (b₀, (0 : Fin m → ℂ)), k bz ∈ ball (0 : Fin g → ℂ) (r₀ / 2) :=
    hkc.eventually_mem (by rw [hk0]; exact ball_mem_nhds _ (half_pos hr₀))
  obtain ⟨W₂, hW₂, hb₀W₂, r, hr, hbox⟩ := box_of_eventually (hev.and hsmall)
  have hWB : ∀ b ∈ W₂, b ∈ B' := fun b hb => (hbox b hb 0 (mem_ball_self hr)).1.2.2
  obtain ⟨hl, hl1, hl2⟩ := lift_of_local (P := fun b => Over.mk (spMap (ψ b)) ⟶ G) e.ex u k
    (hW₁.inter hW₂) hr hr₀
    (fun b hb => e.add b (hsub (hWB b hb.2)))
    (fun b hb => hu b (hWB b hb.2))
    (fun b hb => hinj b hb.1)
    (fun b hb z hz => ⟨(hbox b hb.2 z hz).1.1, (hbox b hb.2 z hz).1.2.1, (hbox b hb.2 z hz).2⟩)
  exact ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hb₀W₁, hb₀W₂⟩, fun b hb => hWB b hb.2, hl, hl1, hl2⟩

end Scheme

/- English proof (translation)
Establish `hL0 : L 0 = 0` using `map_zero L`. Establish `hchain : ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → (fderiv ℂ (fun z => valAt' (e (L z)) U f) 0) w = (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L w)`. Introduce `U h f hv`. Establish `hU : ⊤ ≤ e 0 ⁻¹ᵁ U`. Rewrite using `[← hv]`.

Conclude with `fun x _ => h (Set.mem_univ _)`. Establish `hd' : DifferentiableAt ℂ (fun z => valAt' (e z) U f) ((LinearMap.toContinuousLinearMap L) 0)`. Rewrite using `[map_zero]`. Conclude with `he U f hU`. Establish `hLc : (fun z => valAt' (e (L z)) U f) = (fun z => valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L)`.

Use function extensionality and compare the values at `z`. Both sides reduce to the same expression. Rewrite using `[hLc, fderiv_comp 0 hd' (LinearMap.toContinuousLinearMap L).differentiableAt, ContinuousLinearMap.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, map_zero, LinearMap.coe_toContinuousLinearMap']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Establish `hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0` using `h1.trans (congrArg e hL0)`. Conclude with `⟨hv, fun U h f => (h2 U h f).trans (hchain U h f hv)⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1.trans (congrArg e hL0).symm, fun U h f => (h2 U h f).trans (hchain U h f h1).symm⟩`.
-/
theorem isDerivAt0_comp_lin {g m : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : ∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ e 0 ⁻¹ᵁ U →
      DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0)
    (L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin m → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have hL0 : L 0 = 0 := map_zero L
  have hchain : ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      (fderiv ℂ (fun z => valAt' (e (L z)) U f) 0) w = (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L w) := by
    intro U h f hv
    have hU : ⊤ ≤ e 0 ⁻¹ᵁ U := by
      rw [← hv]
      exact fun x _ => h (Set.mem_univ _)
    have hd' : DifferentiableAt ℂ (fun z => valAt' (e z) U f) ((LinearMap.toContinuousLinearMap L) 0) := by
      rw [map_zero]
      exact he U f hU
    have hLc : (fun z => valAt' (e (L z)) U f) =
        (fun z => valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L) := by
      funext z
      rfl
    rw [hLc, fderiv_comp 0 hd' (LinearMap.toContinuousLinearMap L).differentiableAt,
      ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.comp_apply, map_zero, LinearMap.coe_toContinuousLinearMap']
  constructor
  · rintro ⟨h1, h2⟩
    have hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := h1.trans (congrArg e hL0)
    exact ⟨hv, fun U h f => (h2 U h f).trans (hchain U h f hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans (congrArg e hL0).symm, fun U h f => (h2 U h f).trans (hchain U h f h1).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.ExpLift

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ExpLift in

/- English proof (translation)
Introduce `R _ G _ _ g n M B ψ e m B' u hB' hsub hu hhol`. Establish `hloc` using `fun b (hb : b ∈ B') => exists_local_linear e u hsub hu hhol hb`. Establish `huniq : ∀ b ∈ B', ∀ h₁ h₂ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, e.ex b (h₁ z) = u b z) → (∀ z, e.ex b (h₂ z) = u b z) → h₁ = h₂`. Introduce `b hb h₁ h₂ e₁ e₂`. Take `⟨W, -, hbW, r, hr, hinj⟩` from `ex_inj_near e (hsub hb)`.

Conclude with `linear_unique (e.ex b) hr (hinj b hbW) h₁ h₂ (fun z => (e₁ z).trans (e₂ z).symm)`. Establish `hexl : ∀ b ∈ B', ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (L z) = u b z`. Introduce `b hb`. Take `⟨W, -, hbW, -, hl, hl1, -⟩` from `hloc b hb`. Conclude with `⟨hl b, hl1 b hbW⟩`.

Set `h : (Fin n → ℂ) → ((Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ))` to `fun b => if hb : ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (L z) = u b z then hb.choose else 0`. Establish `hh : ∀ b ∈ B', ∀ z, e.ex b (h b z) = u b z`. Introduce `b hb`. Establish `hx` using `hexl b hb`. Rewrite using `[show h b = hx.choose from dif_pos hx]`.

Conclude with `hx.choose_spec`. Use `⟨h, ?_, fun b hb => ⟨hh b hb, fun h' hh' => huniq b hb h' (h b) hh' (hh b hb), fun z v => ?_⟩⟩` and prove the remaining obligations. Introduce `z b₀ hb₀`. Take `⟨W, hW, hb₀W, hWB, hl, hl1, hl2⟩` from `hloc b₀ hb₀`. Establish `heq : (fun b => hl b z) =ᶠ[𝓝 b₀] fun b => h b z` using `by filter_upwards [hW.mem_nhds hb₀W] with b hb`.

Rewrite using `[huniq b (hWB hb) (hl b) (h b) (hl1 b hb) (hh b (hWB hb))]`. Conclude with `(((hl2 z b₀ hb₀W).differentiableAt (hW.mem_nhds hb₀W)).congr_of_eventuallyEq heq.symm).differentiableWithinAt`. Establish `hfun : (fun z => (u b z).left) = fun z => (e.ex b (h b z)).left`. Use function extensionality and compare the values at `z`. Rewrite using `[hh b hb z]`.

Rewrite using `[hfun]`. Conclude with `isDerivAt0_comp_lin (fun z => (e.ex b z).left) (fun U f hU => ex_differentiableAt e (hsub hb) U f hU) (h b) z v`.
-/
theorem exists_linear_lift_of_additive_family : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ) (m : ℕ) (B' : Set (Fin n → ℂ)) (u : ∀ b : Fin n → ℂ, (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), IsOpen B' → B' ⊆ B → (∀ b ∈ B', ∀ z w, u b (z + w) = u b z * u b w) → IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin m → ℂ) => (u bz.1 bz.2).left) → ∃ h : (Fin n → ℂ) → ((Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, DifferentiableOn ℂ (fun b => h b z) B') ∧ ∀ b ∈ B', (∀ z, e.ex b (h b z) = u b z) ∧ (∀ h' : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, e.ex b (h' z) = u b z) → h' = h b) ∧ ∀ z v, IsDerivAt0 (fun z => (u b z).left) z v ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h b z) v := by
  intro R _ G _ _ g n M B ψ e m B' u hB' hsub hu hhol
  classical
  have hloc := fun b (hb : b ∈ B') => exists_local_linear e u hsub hu hhol hb
  have huniq : ∀ b ∈ B', ∀ h₁ h₂ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, e.ex b (h₁ z) = u b z) →
      (∀ z, e.ex b (h₂ z) = u b z) → h₁ = h₂ := by
    intro b hb h₁ h₂ e₁ e₂
    obtain ⟨W, -, hbW, r, hr, hinj⟩ := ex_inj_near e (hsub hb)
    exact linear_unique (e.ex b) hr (hinj b hbW) h₁ h₂ (fun z => (e₁ z).trans (e₂ z).symm)
  have hexl : ∀ b ∈ B', ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (L z) = u b z := by
    intro b hb
    obtain ⟨W, -, hbW, -, hl, hl1, -⟩ := hloc b hb
    exact ⟨hl b, hl1 b hbW⟩
  let h : (Fin n → ℂ) → ((Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun b =>
    if hb : ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (L z) = u b z then hb.choose else 0
  have hh : ∀ b ∈ B', ∀ z, e.ex b (h b z) = u b z := by
    intro b hb
    have hx := hexl b hb
    rw [show h b = hx.choose from dif_pos hx]
    exact hx.choose_spec
  refine ⟨h, ?_, fun b hb => ⟨hh b hb, fun h' hh' => huniq b hb h' (h b) hh' (hh b hb), fun z v => ?_⟩⟩
  · intro z b₀ hb₀
    obtain ⟨W, hW, hb₀W, hWB, hl, hl1, hl2⟩ := hloc b₀ hb₀
    have heq : (fun b => hl b z) =ᶠ[𝓝 b₀] fun b => h b z := by
      filter_upwards [hW.mem_nhds hb₀W] with b hb
      rw [huniq b (hWB hb) (hl b) (h b) (hl1 b hb) (hh b (hWB hb))]
    exact (((hl2 z b₀ hb₀W).differentiableAt (hW.mem_nhds hb₀W)).congr_of_eventuallyEq
      heq.symm).differentiableWithinAt
  · have hfun : (fun z => (u b z).left) = fun z => (e.ex b (h b z)).left := by
      funext z
      rw [hh b hb z]
    rw [hfun]
    exact isDerivAt0_comp_lin (fun z => (e.ex b z).left)
      (fun U f hU => ex_differentiableAt e (hsub hb) U f hU) (h b) z v

end GlobalTheory.CompanionTheory.Ar.Flat
