import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepB

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

/- English proof (translation)
Introduce `y hy`. Use `set i := A.pick y`. Establish `hsrc : (A.chart i).source ∩ U ∈ 𝓝 y` using `((A.chart i).open_source.inter hU).mem_nhds ⟨A.mem_pick y, hy⟩`. Establish `h1 : ContinuousOn (a i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(ha.1 i).continuousOn`. Establish `h2 : ContinuousOn (a i) ((A.chart i).source ∩ U)`.

Use `h1.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) (fun x (hx : x ∈ (A.chart i).source ∩ U) => ⟨(A.chart i).map_source hx.1, by simpa [(A.chart i).left_inv hx.1] using hx.2⟩)` as an intermediate fact. Conclude with `this.congr fun x hx => by simp [(A.chart i).left_inv hx.1]`. Establish `hc : ContinuousAt (fun x => ‖a i x‖ ^ 2 * Real.exp (-A.ph la i x)) y`. Establish `h3` using `h2.continuousAt hsrc`. Establish `h4` using `(bsA_ph_cont A la i).continuousAt ((A.chart i).open_source.mem_nhds (A.mem_pick y))`.

Conclude with `(h3.norm.pow 2).mul (h4.neg.rexp)`. Use `(hc.congr ?_).continuousWithinAt` and prove the remaining obligations. Use `filter_upwards [hsrc] with x hx`. Conclude with `(bsA_nsq_chart A ha.2 hx.2 hx.1).symm`.
-/
theorem bsC_nsq_contOn {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : A.IsSecOn la U a)
    (hU : IsOpen U) : ContinuousOn (A.nsq la a) U := by
  intro y hy
  set i := A.pick y
  have hsrc : (A.chart i).source ∩ U ∈ 𝓝 y :=
    ((A.chart i).open_source.inter hU).mem_nhds ⟨A.mem_pick y, hy⟩
  have h1 : ContinuousOn (a i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (ha.1 i).continuousOn
  have h2 : ContinuousOn (a i) ((A.chart i).source ∩ U) := by
    have := h1.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
      (fun x (hx : x ∈ (A.chart i).source ∩ U) => ⟨(A.chart i).map_source hx.1, by simpa [(A.chart i).left_inv hx.1] using hx.2⟩)
    exact this.congr fun x hx => by simp [(A.chart i).left_inv hx.1]
  have hc : ContinuousAt (fun x => ‖a i x‖ ^ 2 * Real.exp (-A.ph la i x)) y := by
    have h3 := h2.continuousAt hsrc
    have h4 := (bsA_ph_cont A la i).continuousAt
      ((A.chart i).open_source.mem_nhds (A.mem_pick y))
    exact (h3.norm.pow 2).mul (h4.neg.rexp)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hsrc] with x hx
  exact (bsA_nsq_chart A ha.2 hx.2 hx.1).symm

/- English proof (translation)
Unfold `nsq`. Rewrite using `[hq, A.ph_add la (m • L) _ y (A.mem_pick y), bsA_ph_nsmul A L m (A.mem_pick y)]`. Rewrite using `[norm_mul, norm_mul, norm_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, neg_add, Real.exp_add, show -((m : ℝ) * A.ph L (A.pick y) y) = (m : ℝ) * (-A.ph L (A.pick y) y) by ring, Real.exp_nat_mul, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bsC_nsq_prod (la L : La) (m : ℕ) (q u v : ι → Y → ℂ) (c : ℂ) (y : Y)
    (hq : q (A.pick y) y = c * (u (A.pick y) y * v (A.pick y) y ^ m)) :
    A.nsq (la + m • L) q y = ‖c‖ ^ 2 * A.nsq la u y * A.nsq L v y ^ m := by
  unfold nsq
  rw [hq, A.ph_add la (m • L) _ y (A.mem_pick y), bsA_ph_nsmul A L m (A.mem_pick y)]
  rw [norm_mul, norm_mul, norm_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, neg_add,
    Real.exp_add, show -((m : ℝ) * A.ph L (A.pick y) y) = (m : ℝ) * (-A.ph L (A.pick y) y) by ring,
    Real.exp_nat_mul, ← pow_mul]
  ring

/- English proof (translation)
Unfold `sqn nsq`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: ‖w0 (A.pick y) y‖ ≠ 0` using `norm_ne_zero_iff.mpr h0`. Rewrite using `[norm_div, div_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem bsC_sqn_ratio {N : ℕ} (la : La) (u : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (y : Y)
    (h0 : w0 (A.pick y) y ≠ 0) :
    A.sqn la u y = A.nsq la w0 y * ∑ k, ‖u k (A.pick y) y / w0 (A.pick y) y‖ ^ 2 := by
  unfold sqn nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ‖w0 (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [norm_div, div_pow]
  field_simp

/- English proof (translation)
Rewrite using `[Real.mul_rpow ha.le hZ.le, Real.mul_rpow ha.le hS.le]`. Establish `key : a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ)) = 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_add ha, ← Real.rpow_add ha]`. Put the polynomial expressions in normal form. Conclude with `Real.rpow_zero a`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bsC_alg (Fn nσ a Z S ρ : ℝ) (m : ℕ) (ha : 0 < a) (hZ : 0 < Z) (hS : 0 < S) :
    Fn * nσ * a ^ m * (a * Z) ^ (-((m : ℝ) - 1 / 2)) * (a * S) ^ (-(1 / 2 : ℝ)) * ρ =
      Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) := by
  rw [Real.mul_rpow ha.le hZ.le, Real.mul_rpow ha.le hS.le]
  have key : a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha, ← Real.rpow_add ha]
    ring_nf; exact Real.rpow_zero a
  calc Fn * nσ * a ^ m * (a ^ (-((m : ℝ) - 1 / 2)) * Z ^ (-((m : ℝ) - 1 / 2))) *
        (a ^ (-(1 / 2 : ℝ)) * S ^ (-(1 / 2 : ℝ))) * ρ
      = Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) *
          (a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [key, mul_one]

/- English proof (translation)
Unfold `bsPh0 bsPsi`. Establish `hd2 : 0 < ‖(jz A w0 s (A.pick y) y).det‖ ^ 2` using `by positivity`. Rewrite using `[Real.rpow_def_of_pos hS]`. Rewrite using `[show -(-Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y + Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) + 1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)) = Real.log (A.nsq mu0 σ y) + A.ph A.kap (A.pick y) y - Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) + R …`. Rewrite using `[Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hσ, Real.exp_log hd2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_neg_frameWeight_eq {N : ℕ} (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (mu0 : La) (σ : ι → Y → ℂ) (y : Y) (hσ : 0 < A.nsq mu0 σ y)
    (hd : (jz A w0 s (A.pick y) y).det ≠ 0)
    (hS : 0 < ∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) :
    Real.exp (-bsPh0 A w w0 s mu0 σ y) =
      A.nsq mu0 σ y * (Real.exp (A.ph A.kap (A.pick y) y) / ‖(jz A w0 s (A.pick y) y).det‖ ^ 2) *
        (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  unfold bsPh0 bsPsi
  have hd2 : 0 < ‖(jz A w0 s (A.pick y) y).det‖ ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hS]
  rw [show -(-Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
      Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
      1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)) =
      Real.log (A.nsq mu0 σ y) + A.ph A.kap (A.pick y) y -
        Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
        Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) * (-(1 / 2 : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hσ, Real.exp_log hd2]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
