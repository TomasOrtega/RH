import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

open Topology Filter

namespace BaseB

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun _ => rfl`.
-/
theorem toBot_one : toBot (1 : GQ l) = 1 := AlgEquiv.ext fun _ => rfl

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun _ => rfl`.
-/
theorem toBot_mul (g h : GQ l) : toBot (g * h) = toBot g * toBot h := AlgEquiv.ext fun _ => rfl

/- English proof (translation)
Establish `hm : algebraMap (BdRp l) (BdR l) b ∈ Plus l` using `⟨b, rfl⟩`. Rewrite using `[th, dif_pos hm]`. Use `congr 1`. Conclude with `IsFractionRing.injective (BdRp l) (BdR l) (RingHom.mem_range.1 hm).choose_spec`.
-/
theorem th_alg (b : BdRp l) : th l (algebraMap (BdRp l) (BdR l) b) = θD l b := by
  have hm : algebraMap (BdRp l) (BdR l) b ∈ Plus l := ⟨b, rfl⟩
  rw [th, dif_pos hm]
  congr 1
  exact IsFractionRing.injective (BdRp l) (BdR l) (RingHom.mem_range.1 hm).choose_spec

/- English proof (translation)
The claim follows from `galBdRField_algebraMap _ _`.
-/
theorem σD_alg (g : GQ l) (b : BdRp l) :
    σD g (algebraMap (BdRp l) (BdR l) b) = algebraMap (BdRp l) (BdR l) (toBot g • b) :=
  galBdRField_algebraMap _ _

/- English proof (translation)
The claim follows from `DeRhamTwist.Twist.tQ_eq`.
-/
theorem tQ_alg : tQ l = algebraMap (BdRp l) (BdR l) (tBdR l) := DeRhamTwist.Twist.tQ_eq

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_` and prove the remaining obligations. Set `S` to `MulAction.stabilizer (GQ l) y`. Establish `hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀)`. Rewrite using `[inv_mul_cancel]`. Conclude with `(stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem`.

Use `filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg`. Establish `h : (g₀⁻¹ * g) • y = y` using `hg`. Rewrite `h` using `[mul_smul, inv_smul_eq_iff]`. Conclude with `h`.
-/
theorem orbit_alg (y : PadicAlgCl l) : Continuous fun g : GQ l => g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer (GQ l) y
  have hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg
  have h : (g₀⁻¹ * g) • y = y := hg
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

/- English proof (translation)
Use `show toBot g • (y : ℂ_[l]) = _`. Rewrite using `[gal_smul_coe]`. Both sides reduce to the same expression.
-/
theorem σC_coe (g : GQ l) (y : PadicAlgCl l) : σC g (y : ℂ_[l]) = ((g y : PadicAlgCl l) : ℂ_[l]) := by
  show toBot g • (y : ℂ_[l]) = _
  rw [gal_smul_coe]
  rfl

/- English proof (translation)
The claim follows from `(isometry_smul_gal (toBot g)).dist_eq x y`.
-/
theorem σC_dist (g : GQ l) (x y : ℂ_[l]) : dist (σC g x) (σC g y) = dist x y :=
  (isometry_smul_gal (toBot g)).dist_eq x y

end BaseB

open BaseB

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Introduce `x`. Use `show galBdRField (toBot 1) x = x`. Rewrite using `[toBot_one, galBdRField_one]`. Both sides reduce to the same expression.
-/
theorem base_σD_one : ∀ x, σD (1 : GQ l) x = x := by
  intro x
  show galBdRField (toBot 1) x = x
  rw [toBot_one, galBdRField_one]
  rfl

/- English proof (translation)
Introduce `g h x`. Use `show galBdRField (toBot (g * h)) x = galBdRField (toBot g) (galBdRField (toBot h) x)`. Rewrite using `[toBot_mul, galBdRField_mul]`. Both sides reduce to the same expression.
-/
theorem base_σD_mul : ∀ (g h : GQ l) x, σD (g * h) x = σD g (σD h x) := by
  intro g h x
  show galBdRField (toBot (g * h)) x = galBdRField (toBot g) (galBdRField (toBot h) x)
  rw [toBot_mul, galBdRField_mul]
  rfl

/- English proof (translation)
Introduce `x`. Use `show galCp (toBot 1) x = x`. Rewrite using `[toBot_one, galCp_one]`. Both sides reduce to the same expression.
-/
theorem base_σC_one : ∀ x, σC (1 : GQ l) x = x := by
  intro x
  show galCp (toBot 1) x = x
  rw [toBot_one, galCp_one]
  rfl

/- English proof (translation)
Introduce `g h x`. Use `show galCp (toBot (g * h)) x = galCp (toBot g) (galCp (toBot h) x)`. Rewrite using `[toBot_mul, galCp_mul]`. Both sides reduce to the same expression.
-/
theorem base_σC_mul : ∀ (g h : GQ l) x, σC (g * h) x = σC g (σC h x) := by
  intro g h x
  show galCp (toBot (g * h)) x = galCp (toBot g) (galCp (toBot h) x)
  rw [toBot_mul, galCp_mul]
  rfl

/- English proof (translation)
Introduce `g`. Use `show σD g (algebraMap (BdRp l) (BdR l) (uBdR l)) = _`. Rewrite using `[σD_alg, gal_smul_uBdR_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g), map_add, map_mul, tQ_alg]`. Both sides reduce to the same expression.
-/
theorem base_σ_u : ∀ g : GQ l, σD g (uQ l) = uQ l + qQ l (κ g) * tQ l := by
  intro g
  show σD g (algebraMap (BdRp l) (BdR l) (uBdR l)) = _
  rw [σD_alg, gal_smul_uBdR_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g), map_add,
    map_mul, tQ_alg]
  rfl

/- English proof (translation)
Introduce `g h`. Simplify using `only [κ, χ]`. Rewrite using `[toBot_mul, kummerC_mul, DeRhamTwist.Twist.cycloChar_toBot]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem base_κ_mul : ∀ g h : GQ l, κ (g * h) = κ g + χ g * κ h := by
  intro g h
  simp only [κ, χ]
  rw [toBot_mul, kummerC_mul, DeRhamTwist.Twist.cycloChar_toBot]
  push_cast
  ring

/- English proof (translation)
Introduce and unpack `g _ ⟨b, rfl⟩`. Conclude with `⟨toBot g • b, (σD_alg g b).symm⟩`.
-/
theorem base_plus_σ : ∀ (g : GQ l) x, x ∈ Plus l → σD g x ∈ Plus l := by
  rintro g _ ⟨b, rfl⟩
  exact ⟨toBot g • b, (σD_alg g b).symm⟩

/- English proof (translation)
Introduce and unpack `g _ ⟨b, rfl⟩`. Rewrite using `[σD_alg, th_alg, th_alg]`. Conclude with `thetaBDeRhamPlusField_gal_smul _ _`.
-/
theorem base_th_σ : ∀ (g : GQ l) x, x ∈ Plus l → th l (σD g x) = σC g (th l x) := by
  rintro g _ ⟨b, rfl⟩
  rw [σD_alg, th_alg, th_alg]
  exact thetaBDeRhamPlusField_gal_smul _ _

/- English proof (translation)
Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`. Rewrite using `[← map_add, th_alg, th_alg, th_alg, map_add]`.
-/
theorem base_th_add : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x + y) = th l x + th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_add, th_alg, th_alg, th_alg, map_add]

/- English proof (translation)
Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`. Rewrite using `[← map_mul, th_alg, th_alg, th_alg, map_mul]`.
-/
theorem base_th_mul : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x * y) = th l x * th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, th_alg, th_alg, th_alg, map_mul]

/- English proof (translation)
Introduce `q`. Use `⟨⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show th l (algebraMap (BdRp l) (BdR l) (algebraMap ℚ_[l] (BdRp l) q)) = _`. Rewrite using `[th_alg]`. Conclude with `thetaBDeRhamPlusField_algebraMap l q`.
-/
theorem base_th_q : ∀ q, qQ l q ∈ Plus l ∧ th l (qQ l q) = algebraMap ℚ_[l] ℂ_[l] q := by
  intro q
  refine ⟨⟨_, rfl⟩, ?_⟩
  show th l (algebraMap (BdRp l) (BdR l) (algebraMap ℚ_[l] (BdRp l) q)) = _
  rw [th_alg]
  exact thetaBDeRhamPlusField_algebraMap l q

/- English proof (translation)
Assemble the required witnesses or components as `⟨ACris.iota ℂ_[l] l (tA l), rfl⟩`.
-/
theorem base_t_plus : tQ l ∈ Plus l := ⟨ACris.iota ℂ_[l] l (tA l), rfl⟩

/- English proof (translation)
Introduce and unpack `_ ⟨b, rfl⟩`. Rewrite using `[th_alg]`. Establish `hk : θD l b = 0 ↔ b ∈ IsLocalRing.maximalIdeal (BdRp l)`. Rewrite using `[IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]`. Both sides reduce to the same expression.

Rewrite using `[hk, maximalIdeal_eq_span_tBdR, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨_, ⟨c, rfl⟩, by rw [← hc, tQ_alg, ← map_mul, mul_comm]⟩`. Introduce and unpack `⟨_, ⟨c, rfl⟩, h⟩`.

Use `⟨c, IsFractionRing.injective (BdRp l) (BdR l) ?_⟩` and prove the remaining obligations. Rewrite using `[h, tQ_alg, ← map_mul, mul_comm]`.
-/
theorem base_th_zero : ∀ x ∈ Plus l, (th l x = 0 ↔ ∃ y ∈ Plus l, x = tQ l * y) := by
  rintro _ ⟨b, rfl⟩
  rw [th_alg]
  have hk : θD l b = 0 ↔ b ∈ IsLocalRing.maximalIdeal (BdRp l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]
    rfl
  rw [hk, maximalIdeal_eq_span_tBdR, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨_, ⟨c, rfl⟩, by rw [← hc, tQ_alg, ← map_mul, mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, h⟩
    refine ⟨c, IsFractionRing.injective (BdRp l) (BdR l) ?_⟩
    rw [h, tQ_alg, ← map_mul, mul_comm]

/- English proof (translation)
Introduce `x hx`. Take `⟨i, u, h⟩` from `ACris.exists_eq_zpow_mul_unit untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hx`. Use `⟨i, algebraMap (BdRp l) (BdR l) (u : BdRp l), algebraMap (BdRp l) (BdR l) ((u⁻¹ : (BdRp l)ˣ) : BdRp l), ⟨_, rfl⟩, ⟨_, rfl⟩, by rw [← map_mul, Units.mul_inv, map_one], ?_⟩` and prove the remaining obligations. Rewrite using `[h, tQ_alg]`. Both sides reduce to the same expression.
-/
theorem base_val : ∀ x : BdR l, x ≠ 0 → ∃ (i : ℤ) (u v : BdR l), u ∈ Plus l ∧ v ∈ Plus l ∧ u * v = 1 ∧
    x = tQ l ^ i * u := by
  intro x hx
  obtain ⟨i, u, h⟩ := ACris.exists_eq_zpow_mul_unit untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hx
  refine ⟨i, algebraMap (BdRp l) (BdR l) (u : BdRp l), algebraMap (BdRp l) (BdR l) ((u⁻¹ : (BdRp l)ˣ) : BdRp l),
    ⟨_, rfl⟩, ⟨_, rfl⟩, by rw [← map_mul, Units.mul_inv, map_one], ?_⟩
  rw [h, tQ_alg]
  rfl

/- English proof (translation)
Introduce `x`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`.

Take `⟨_, ⟨y, rfl⟩, hxy⟩` from `Metric.mem_closure_iff.1 (UniformSpace.Completion.denseRange_coe x) (ε / 3) (by positivity)`. Establish `hc` using `(UniformSpace.Completion.continuous_coe (PadicAlgCl l)).comp (orbit_alg (l := l) y)`. Use `filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto g₀) (ε / 3) (by positivity)] with g hg`. Establish `h1 : dist (((g y : PadicAlgCl l) : ℂ_[l])) (((g₀ y : PadicAlgCl l) : ℂ_[l])) < ε / 3` using `hg`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[σC_dist, σC_dist, σC_coe, σC_coe, dist_comm (y : ℂ_[l]) x]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem base_orbit : ∀ x : ℂ_[l], Continuous fun g : GQ l => σC g x := by
  intro x
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 (UniformSpace.Completion.denseRange_coe x) (ε / 3)
    (by positivity)
  have hc := (UniformSpace.Completion.continuous_coe (PadicAlgCl l)).comp (orbit_alg (l := l) y)
  filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto g₀) (ε / 3) (by positivity)] with g hg
  have h1 : dist (((g y : PadicAlgCl l) : ℂ_[l])) (((g₀ y : PadicAlgCl l) : ℂ_[l])) < ε / 3 := hg
  calc dist (σC g x) (σC g₀ x)
      ≤ dist (σC g x) (σC g (y : ℂ_[l])) + dist (σC g (y : ℂ_[l])) (σC g₀ (y : ℂ_[l])) +
          dist (σC g₀ (y : ℂ_[l])) (σC g₀ x) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [σC_dist, σC_dist, σC_coe, σC_coe, dist_comm (y : ℂ_[l]) x]
      linarith

end period_ring_base
