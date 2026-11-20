import Mathlib
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureCosets
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing ENNReal NNReal nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

section Invariant

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x ↦ ?_` and prove the remaining obligations. Establish `hU : (fun y ↦ x⁻¹ * y) ⁻¹' (W : Set G) ∈ 𝓝 x` using `(hW.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [W.one_mem])`. Use `(continuousAt_const (y := F x)).congr ?_` and prove the remaining obligations. Use `filter_upwards [hU] with y hy`. Establish `hy' : x⁻¹ * y ∈ W` using `hy`.

Use `hF x _ hy'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.
-/
theorem continuous_of_forall_mul_eq {X : Type*} [TopologicalSpace X] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) {F : G → X} (hF : ∀ x, ∀ w ∈ W, F (x * w) = F x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hU : (fun y ↦ x⁻¹ * y) ⁻¹' (W : Set G) ∈ 𝓝 x :=
    (hW.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [W.one_mem])
  refine (continuousAt_const (y := F x)).congr ?_
  filter_upwards [hU] with y hy
  have hy' : x⁻¹ * y ∈ W := hy
  have := hF x _ hy'
  rw [mul_inv_cancel_left] at this
  exact this.symm

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `hc : Countable (G ⧸ W)` using `countable_quotient_of_isOpen hW`. Establish `: DiscreteTopology (G ⧸ W)` using `QuotientGroup.discreteTopology hW`. Use `set S : G ⧸ W → Set G := fun c ↦ QuotientGroup.mk ⁻¹' {c}`. Establish `hSm : ∀ c, MeasurableSet (S c)` using `fun c ↦ ((isOpen_discrete ({c} : Set (G ⧸ W))).preimage QuotientGroup.continuous_mk).measurableSet`. Establish `hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set G)`.

Introduce `c`. Use extensionality with `b`. Simplify using `only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' c]`. Rewrite using `[eq_comm, QuotientGroup.eq]`.

Establish `hd : Pairwise (Function.onFun Disjoint S)`. Introduce `c d hcd`. Use `Set.disjoint_left.2 fun p hp hq ↦ hcd ?_` and prove the remaining obligations. Conclude with `hp.symm.trans hq`. Establish `hu : ⋃ c, S c = Set.univ` using `Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p : G ⧸ W), rfl⟩`.

Rewrite using `[← setLIntegral_univ, ← hu, lintegral_iUnion hSm hd]`. Use `tsum_congr fun c ↦ ?_` and prove the remaining obligations. Establish `hconst : ∀ b ∈ S c, F b = F c.out`. Introduce `b hb`. Rewrite `hb` using `[hSW c]`.

Establish `hb' : c.out⁻¹ * b ∈ W` using `hb`. Use `hF c.out _ hb'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[setLIntegral_congr_fun (hSm c) hconst, setLIntegral_const, hSW c, measure_preimage_mul]`.
-/
theorem lintegral_eq_tsum_of_forall_mul_eq (μ : Measure G) [μ.IsMulLeftInvariant]
    {W : Subgroup G} (hW : IsOpen (W : Set G)) {F : G → ℝ≥0∞}
    (hF : ∀ x, ∀ w ∈ W, F (x * w) = F x) :
    ∫⁻ x, F x ∂μ = ∑' c : G ⧸ W, F c.out * μ W := by
  have hc : Countable (G ⧸ W) := countable_quotient_of_isOpen hW
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW
  set S : G ⧸ W → Set G := fun c ↦ QuotientGroup.mk ⁻¹' {c}
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    ((isOpen_discrete ({c} : Set (G ⧸ W))).preimage QuotientGroup.continuous_mk).measurableSet
  have hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set G) := by
    intro c
    ext b
    simp only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq]
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun p hp hq ↦ hcd ?_
    exact hp.symm.trans hq
  have hu : ⋃ c, S c = Set.univ :=
    Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p : G ⧸ W), rfl⟩
  rw [← setLIntegral_univ, ← hu, lintegral_iUnion hSm hd]
  refine tsum_congr fun c ↦ ?_
  have hconst : ∀ b ∈ S c, F b = F c.out := by
    intro b hb
    rw [hSW c] at hb
    have hb' : c.out⁻¹ * b ∈ W := hb
    have := hF c.out _ hb'
    rwa [mul_inv_cancel_left] at this
  rw [setLIntegral_congr_fun (hSm c) hconst, setLIntegral_const, hSW c, measure_preimage_mul]

end Invariant

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup WithZero

/- English proof (translation)
The claim follows from `Nat.cast_pos.2 (lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v))`.
-/
theorem absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
  Nat.cast_pos.2 (lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v))

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, Valued.v ((x : 𝔸[K]).2 v) = exp n` from `⟨_, (exp_log (valued_ne_zero v x)).symm⟩`. Rewrite using `[FinitePlace.norm_def, ord, hn, log_exp, Int.cast_neg, neg_neg, WithZeroMulInt.toNNReal_neg_apply _ (exp_ne_zero)]`. Simplify using `only [NNReal.coe_zpow, NNReal.coe_natCast, Real.rpow_intCast]`. Use `congr 1`.
-/
theorem norm_finite_eq_rpow (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(x : 𝔸[K]).2 v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ord v x : ℝ)) := by
  obtain ⟨n, hn⟩ : ∃ n, Valued.v ((x : 𝔸[K]).2 v) = exp n :=
    ⟨_, (exp_log (valued_ne_zero v x)).symm⟩
  rw [FinitePlace.norm_def, ord, hn, log_exp, Int.cast_neg, neg_neg,
    WithZeroMulInt.toNNReal_neg_apply _ (exp_ne_zero)]
  simp only [NNReal.coe_zpow, NNReal.coe_natCast, Real.rpow_intCast]
  congr 1

def zetaWeight (σ : ℝ) (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : ℝ :=
  n.prod fun v k ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(σ * k))

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun v _ ↦ (Real.rpow_pos_of_pos (absNorm_asIdeal_pos v) _).le`.
-/
theorem zetaWeight_nonneg (σ : ℝ) (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : 0 ≤ zetaWeight σ n :=
  Finset.prod_nonneg fun v _ ↦ (Real.rpow_pos_of_pos (absNorm_asIdeal_pos v) _).le

/- English proof (translation)
Use `Finsupp.prod_add_index' (fun v ↦ by simp) fun v a b ↦ ?_` and prove the remaining obligations. Rewrite using `[Int.cast_add, mul_add, neg_add, Real.rpow_add (absNorm_asIdeal_pos v)]`.
-/
theorem zetaWeight_add (σ : ℝ) (n m : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    zetaWeight σ (n + m) = zetaWeight σ n * zetaWeight σ m := by
  refine Finsupp.prod_add_index' (fun v ↦ by simp) fun v a b ↦ ?_
  rw [Int.cast_add, mul_add, neg_add, Real.rpow_add (absNorm_asIdeal_pos v)]

/- English proof (translation)
Establish `hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : 𝔸[K]).2 v‖) ⊆ ((ordFinsupp K x).support : Set _)`. Introduce `v hv`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h`. Apply `hv` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `ord v x = 0 at h`. Use `show ‖(x : 𝔸[K]).2 v‖ = 1`. Rewrite using `[norm_finite_eq_rpow, h, Int.cast_zero, neg_zero, Real.rpow_zero]`. Rewrite using `[finiteModule, finprod_eq_prod_of_mulSupport_subset _ hsub, zetaWeight, Finsupp.prod, ← Real.finsetProd_rpow _ _ (fun v _ ↦ norm_nonneg _)]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[norm_finite_eq_rpow, ← Real.rpow_mul (absNorm_asIdeal_pos v).le]`. Express the relevant statement in the definitionally equal form `_ = _ ^ (-(σ * (ord v x : ℝ)))`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finiteModule_rpow_eq (x : IdeleGroup K) (σ : ℝ) :
    finiteModule x ^ σ = zetaWeight σ (ordFinsupp K x) := by
  classical
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : 𝔸[K]).2 v‖) ⊆
      ((ordFinsupp K x).support : Set _) := by
    intro v hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hv
    change ord v x = 0 at h
    show ‖(x : 𝔸[K]).2 v‖ = 1
    rw [norm_finite_eq_rpow, h, Int.cast_zero, neg_zero, Real.rpow_zero]
  rw [finiteModule, finprod_eq_prod_of_mulSupport_subset _ hsub, zetaWeight, Finsupp.prod,
    ← Real.finsetProd_rpow _ _ (fun v _ ↦ norm_nonneg _)]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [norm_finite_eq_rpow, ← Real.rpow_mul (absNorm_asIdeal_pos v).le]
  change _ = _ ^ (-(σ * (ord v x : ℝ)))
  congr 1
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofFinite_val_snd (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((ofFinite b : IdeleGroup K) : 𝔸[K]).2 = b := rfl

/- English proof (translation)
Rewrite using `[mem_idealFiniteAdeles]`. Use `forall_congr' fun v ↦ ?_` and prove the remaining obligations. Establish `h` using `valued_ne_zero v (ofFinite b)`. Rewrite `h` using `[ofFinite_val_snd]`. Rewrite using `[ord, ofFinite_val_snd, ← log_le_iff_le_exp h]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mem_idealFiniteAdeles_iff_ord (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) ≤ ord v (ofFinite b) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun v ↦ ?_
  have h := valued_ne_zero v (ofFinite b)
  rw [ofFinite_val_snd] at h
  rw [ord, ofFinite_val_snd, ← log_le_iff_le_exp h]
  omega

/- English proof (translation)
Establish `hw' : ofFinite w ∈ standardOpenSubgroup K` using `hw`. Rewrite `hw'` using `[mem_standardOpenSubgroup_iff_ord]`. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `ord v (ofFinite (b * w)) = ord v (ofFinite b)`. Rewrite using `[map_mul, ord_mul, hw' v, add_zero]`.
-/
theorem ordFinsupp_ofFinite_mul (b : (FiniteAdeleRing (𝓞 K) K)ˣ)
    {w : (FiniteAdeleRing (𝓞 K) K)ˣ} (hw : w ∈ finiteIntegralUnits K) :
    ordFinsupp K (ofFinite (b * w)) = ordFinsupp K (ofFinite b) := by
  have hw' : ofFinite w ∈ standardOpenSubgroup K := hw
  rw [mem_standardOpenSubgroup_iff_ord] at hw'
  ext v
  change ord v (ofFinite (b * w)) = ord v (ofFinite b)
  rw [map_mul, ord_mul, hw' v, add_zero]

/- English proof (translation)
Introduce `c d h`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq]`. Express the relevant statement in the definitionally equal form `ofFinite (c.out⁻¹ * d.out) ∈ standardOpenSubgroup K`. Rewrite using `[mem_standardOpenSubgroup_iff_ord]`. Introduce `v`.

Use `congrArg (fun f ↦ f v) h` as an intermediate fact. Express the relevant statement in the definitionally equal form `ord v (ofFinite c.out) = ord v (ofFinite d.out) at this`. Rewrite using `[map_mul, map_inv, ord_mul, ord_inv, this]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordFinsupp_ofFinite_out_injective :
    Function.Injective fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦
      ordFinsupp K (ofFinite c.out) := by
  intro c d h
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq]
  change ofFinite (c.out⁻¹ * d.out) ∈ standardOpenSubgroup K
  rw [mem_standardOpenSubgroup_iff_ord]
  intro v
  have := congrArg (fun f ↦ f v) h
  change ord v (ofFinite c.out) = ord v (ofFinite d.out) at this
  rw [map_mul, map_inv, ord_mul, ord_inv, this]
  omega

open Classical in

def zetaTerm (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ) (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : ℝ :=
  if ∀ v, FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) ≤ n v then zetaWeight σ n
  else 0

/- English proof (translation)
Unfold `zetaTerm`. Use `split_ifs`. Use `exacts [zetaWeight_nonneg _ _, le_rfl]`.
-/
theorem zetaTerm_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ)
    (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : 0 ≤ zetaTerm L σ n := by
  unfold zetaTerm
  split_ifs
  exacts [zetaWeight_nonneg _ _, le_rfl]

def countFinsupp (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K))
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _))

def idealOfExponents (k : HeightOneSpectrum (𝓞 K) →₀ ℤ) : Ideal (𝓞 K) :=
  k.prod fun v n ↦ v.asIdeal ^ n.toNat

/- English proof (translation)
Rewrite using `[idealOfExponents, Finsupp.prod, Finsupp.prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_pow, FractionalIdeal.coeIdealHom_apply, ← zpow_natCast, Int.toNat_of_nonneg (hk v)]`.
-/
theorem coeIdeal_idealOfExponents {k : HeightOneSpectrum (𝓞 K) →₀ ℤ} (hk : ∀ v, 0 ≤ k v) :
    ((idealOfExponents k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      k.prod fun v n ↦ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n := by
  rw [idealOfExponents, Finsupp.prod, Finsupp.prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [map_pow, FractionalIdeal.coeIdealHom_apply, ← zpow_natCast, Int.toNat_of_nonneg (hk v)]

/- English proof (translation)
Introduce `k hk l hl h`. Use extensionality with `v`. Use `congrArg (fun I : Ideal (𝓞 K) ↦ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) h` as an intermediate fact. Simplify using `only [coeIdeal_idealOfExponents hk, coeIdeal_idealOfExponents hl, FractionalIdeal.count_finsuppProd] at this`. Conclude with `this`.
-/
theorem idealOfExponents_injOn :
    Set.InjOn (idealOfExponents (K := K)) {k | ∀ v, 0 ≤ k v} := by
  intro k hk l hl h
  ext v
  have := congrArg (fun I : Ideal (𝓞 K) ↦
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) h
  simp only [coeIdeal_idealOfExponents hk, coeIdeal_idealOfExponents hl,
    FractionalIdeal.count_finsuppProd] at this
  exact this

/- English proof (translation)
Rewrite using `[idealOfExponents, Finsupp.prod, map_prod, Nat.cast_prod, zetaWeight, Finsupp.prod, ← Real.finsetProd_rpow _ _ (fun v _ ↦ Nat.cast_nonneg _), ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations. Establish `hkv : (((k v).toNat : ℕ) : ℝ) = (k v : ℝ)` using `by exact_mod_cast Int.toNat_of_nonneg (hk v)`. Rewrite using `[map_pow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), hkv]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem zetaWeight_eq_absNorm {σ : ℝ} {k : HeightOneSpectrum (𝓞 K) →₀ ℤ} (hk : ∀ v, 0 ≤ k v) :
    zetaWeight σ k = ((Ideal.absNorm (idealOfExponents k) : ℝ) ^ σ)⁻¹ := by
  rw [idealOfExponents, Finsupp.prod, map_prod, Nat.cast_prod, zetaWeight, Finsupp.prod,
    ← Real.finsetProd_rpow _ _ (fun v _ ↦ Nat.cast_nonneg _), ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hkv : (((k v).toNat : ℕ) : ℝ) = (k v : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hk v)
  rw [map_pow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_neg (Nat.cast_nonneg _), hkv]
  congr 1
  ring

/- English proof (translation)
Use `set m := countFinsupp L`. Use `set S : Set (HeightOneSpectrum (𝓞 K) →₀ ℤ) := {k | ∀ v, 0 ≤ k v}`. Establish `key : ∀ k, zetaTerm L σ (k + m) = zetaWeight σ m * S.indicator (zetaWeight σ) k`. Introduce `k`. Establish `hiff : (∀ v, FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) ≤ (k + m) v) ↔ k ∈ S`.

Use `forall_congr' fun v ↦ ?_` and prove the remaining obligations. Establish `: (k + m) v = k v + FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K)` using `rfl`. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers. Unfold `zetaTerm`.

Rewrite using `[Set.indicator_apply]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[zetaWeight_add, mul_comm]`. Conclude with `absurd (hiff.1 h1) h2`. Conclude with `absurd (hiff.2 h2) h1`.

Rewrite using `[mul_zero]`. Establish `h1 : ∑' n, ENNReal.ofReal (zetaTerm L σ n) = ENNReal.ofReal (zetaWeight σ m) * ∑' k, S.indicator (fun k ↦ ENNReal.ofReal (zetaWeight σ k)) k`. Rewrite using `[← (Equiv.addRight m).tsum_eq, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun k ↦ ?_` and prove the remaining obligations. Use `show ENNReal.ofReal (zetaTerm L σ (k + m)) = _`.

Rewrite using `[key, ENNReal.ofReal_mul (zetaWeight_nonneg _ _)]`. Distinguish the cases in `hk : k ∈ S`. Rewrite using `[Set.indicator_of_mem hk, Set.indicator_of_mem hk]`. Rewrite using `[Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, ENNReal.ofReal_zero]`. Rewrite using `[h1]`.

Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Rewrite using `[← tsum_subtype S]`. Establish `hinj : Function.Injective fun k : S ↦ idealOfExponents (k : HeightOneSpectrum (𝓞 K) →₀ ℤ)` using `fun k l h ↦ Subtype.ext (idealOfExponents_injOn k.2 l.2 h)`. Establish `hle : ∑' k : S, ENNReal.ofReal (zetaWeight σ (k : HeightOneSpectrum (𝓞 K) →₀ ℤ)) ≤ ∑' I : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm I : ℝ) ^ σ)⁻¹)`. Use `le_trans (le_of_eq (tsum_congr fun k ↦ ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun I ↦ ENNReal.ofReal (((Ideal.absNorm I : ℝ) ^ σ)⁻¹)))` and prove the remaining obligations.

Rewrite using `[zetaWeight_eq_absNorm k.2]`. Use `hle.trans_lt ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun I ↦ by positivity) (summable_absNorm_rpow_inv hσ)]`. Conclude with `ENNReal.ofReal_lt_top`.
-/
theorem tsum_ofReal_zetaTerm_lt_top (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n, ENNReal.ofReal (zetaTerm L σ n) < ∞ := by
  classical
  set m := countFinsupp L
  set S : Set (HeightOneSpectrum (𝓞 K) →₀ ℤ) := {k | ∀ v, 0 ≤ k v}
  have key : ∀ k, zetaTerm L σ (k + m) = zetaWeight σ m * S.indicator (zetaWeight σ) k := by
    intro k
    have hiff : (∀ v, FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) ≤ (k + m) v) ↔
        k ∈ S := by
      refine forall_congr' fun v ↦ ?_
      have : (k + m) v = k v + FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) := rfl
      rw [this]
      omega
    unfold zetaTerm
    rw [Set.indicator_apply]
    split_ifs with h1 h2 h2
    · rw [zetaWeight_add, mul_comm]
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rw [mul_zero]
  have h1 : ∑' n, ENNReal.ofReal (zetaTerm L σ n) =
      ENNReal.ofReal (zetaWeight σ m) *
        ∑' k, S.indicator (fun k ↦ ENNReal.ofReal (zetaWeight σ k)) k := by
    rw [← (Equiv.addRight m).tsum_eq, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    show ENNReal.ofReal (zetaTerm L σ (k + m)) = _
    rw [key, ENNReal.ofReal_mul (zetaWeight_nonneg _ _)]
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, ENNReal.ofReal_zero]
  rw [h1]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [← tsum_subtype S]
  have hinj : Function.Injective fun k : S ↦ idealOfExponents (k : HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
    fun k l h ↦ Subtype.ext (idealOfExponents_injOn k.2 l.2 h)
  have hle : ∑' k : S, ENNReal.ofReal (zetaWeight σ (k : HeightOneSpectrum (𝓞 K) →₀ ℤ)) ≤
      ∑' I : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm I : ℝ) ^ σ)⁻¹) := by
    refine le_trans (le_of_eq (tsum_congr fun k ↦ ?_))
      (ENNReal.tsum_comp_le_tsum_of_injective hinj
        (fun I ↦ ENNReal.ofReal (((Ideal.absNorm I : ℝ) ^ σ)⁻¹)))
    rw [zetaWeight_eq_absNorm k.2]
  refine hle.trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun I ↦ by positivity) (summable_absNorm_rpow_inv hσ)]
  exact ENNReal.ofReal_lt_top

open Classical in

def finiteZetaBound (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ℝ :=
  if (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L then finiteModule (ofFinite b) ^ σ else 0

/- English proof (translation)
Unfold `finiteZetaBound zetaTerm`. Establish `hiff` using `mem_idealFiniteAdeles_iff_ord L b`. Use `split_ifs with h1 h2 h2`. Rewrite using `[finiteModule_rpow_eq]`. Conclude with `absurd (hiff.1 h1) h2`.

Conclude with `absurd (hiff.2 h2) h1`. Both sides reduce to the same expression.
-/
theorem finiteZetaBound_eq (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finiteZetaBound L σ b = zetaTerm L σ (ordFinsupp K (ofFinite b)) := by
  unfold finiteZetaBound zetaTerm
  have hiff := mem_idealFiniteAdeles_iff_ord L b
  split_ifs with h1 h2 h2
  · rw [finiteModule_rpow_eq]
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

/- English proof (translation)
Rewrite using `[finiteZetaBound_eq]`. Conclude with `zetaTerm_nonneg _ _ _`.
-/
theorem finiteZetaBound_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : 0 ≤ finiteZetaBound L σ b := by
  rw [finiteZetaBound_eq]
  exact zetaTerm_nonneg _ _ _

/- English proof (translation)
Rewrite using `[finiteZetaBound_eq, finiteZetaBound_eq, ordFinsupp_ofFinite_mul b hw]`.
-/
theorem finiteZetaBound_mul (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ)
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) {w : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hw : w ∈ finiteIntegralUnits K) : finiteZetaBound L σ (b * w) = finiteZetaBound L σ b := by
  rw [finiteZetaBound_eq, finiteZetaBound_eq, ordFinsupp_ofFinite_mul b hw]

/- English proof (translation)
The claim follows from `continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits K) fun b _ hw ↦ finiteZetaBound_mul L σ b hw`.
-/
theorem continuous_finiteZetaBound (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σ : ℝ) :
    Continuous (finiteZetaBound L σ) :=
  continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits K) fun b _ hw ↦
    finiteZetaBound_mul L σ b hw

/- English proof (translation)
Use `⟨(continuous_finiteZetaBound L σ).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Eventually.of_forall (finiteZetaBound_nonneg L σ)), lintegral_eq_tsum_of_forall_mul_eq (finiteIdeleMeasure K) (isOpen_finiteIntegralUnits K) (F := fun b ↦ ENNReal.ofReal (finiteZetaBound L σ b)) (fun b w hw ↦ by simp only [finiteZetaBound_mul L σ b …`. Repeatedly rewrite using `[mul_one, finiteZetaBound_eq]`. Conclude with `(ENNReal.tsum_comp_le_tsum_of_injective ordFinsupp_ofFinite_out_injective (fun n ↦ ENNReal.ofReal (zetaTerm L σ n))).trans_lt (tsum_ofReal_zetaTerm_lt_top L hσ)`.
-/
theorem integrable_finiteZetaBound (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (finiteZetaBound L σ) (finiteIdeleMeasure K) := by
  refine ⟨(continuous_finiteZetaBound L σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (finiteZetaBound_nonneg L σ)),
    lintegral_eq_tsum_of_forall_mul_eq (finiteIdeleMeasure K) (isOpen_finiteIntegralUnits K)
      (F := fun b ↦ ENNReal.ofReal (finiteZetaBound L σ b))
      (fun b w hw ↦ by simp only [finiteZetaBound_mul L σ b hw]),
    finiteIdeleMeasure_finiteIntegralUnits]
  simp_rw [mul_one, finiteZetaBound_eq]
  exact (ENNReal.tsum_comp_le_tsum_of_injective ordFinsupp_ofFinite_out_injective
    (fun n ↦ ENNReal.ofReal (zetaTerm L σ n))).trans_lt (tsum_ofReal_zetaTerm_lt_top L hσ)

/- English proof (translation)
Introduce `x hx v`. Use `(hx v).trans ?_` and prove the remaining obligations. Conclude with `exp_le_exp.2 (neg_le_neg (FractionalIdeal.count_mono K v I.ne_zero h))`.
-/
theorem idealFiniteAdeles_subset {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (I : FractionalIdeal (𝓞 K)⁰ K) ≤ J) :
    (idealFiniteAdeles I : Set (FiniteAdeleRing (𝓞 K) K)) ⊆ idealFiniteAdeles J := by
  intro x hx v
  refine (hx v).trans ?_
  exact exp_le_exp.2 (neg_le_neg (FractionalIdeal.count_mono K v I.ne_zero h))

/- English proof (translation)
Use `set e : HeightOneSpectrum (𝓞 K) → ℤ := fun v ↦ -max 0 (log (Valued.v (a v)))`. Establish `he : ∀ᶠ v in Filter.cofinite, e v = 0` using `by filter_upwards [a.2] with v hv`. Establish `h1 : Valued.v (a v) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hv`. Establish `h2 : log (Valued.v (a v)) ≤ 0`. Distinguish the cases in `h0 : Valued.v (a v) = 0`.

Simplify using `[h0]`. Rewrite using `[log_le_iff_le_exp h0, exp_zero]` and apply the resulting hypothesis. Simplify using `[e, h2]`. Use `⟨∏ᶠ v, primeIdealUnit v ^ e v, fun v ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[count_finprod_primeIdealUnit_zpow e he v]`.

Simplify using `only [e, neg_neg]`. Distinguish the cases in `h0 : Valued.v (a v) = 0`. Rewrite using `[h0]`. Conclude with `zero_le`. Use `conv_lhs => rw [← exp_log h0]`.

Conclude with `exp_le_exp.2 (le_max_right _ _)`.
-/
theorem exists_mem_idealFiniteAdeles (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, a ∈ idealFiniteAdeles J := by
  set e : HeightOneSpectrum (𝓞 K) → ℤ := fun v ↦ -max 0 (log (Valued.v (a v)))
  have he : ∀ᶠ v in Filter.cofinite, e v = 0 := by
    filter_upwards [a.2] with v hv
    have h1 : Valued.v (a v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hv
    have h2 : log (Valued.v (a v)) ≤ 0 := by
      by_cases h0 : Valued.v (a v) = 0
      · simp [h0]
      · rwa [log_le_iff_le_exp h0, exp_zero]
    simp [e, h2]
  refine ⟨∏ᶠ v, primeIdealUnit v ^ e v, fun v ↦ ?_⟩
  rw [count_finprod_primeIdealUnit_zpow e he v]
  simp only [e, neg_neg]
  by_cases h0 : Valued.v (a v) = 0
  · rw [h0]
    exact zero_le
  · conv_lhs => rw [← exp_log h0]
    exact exp_le_exp.2 (le_max_right _ _)

def fractionalIdealSupUnit (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 ((I : FractionalIdeal (𝓞 K)⁰ K) ⊔ J) fun h ↦
    I.ne_zero (FractionalIdeal.le_zero_iff.1 (h ▸ le_sup_left))

/- English proof (translation)
Establish `hcov : C ⊆ ⋃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (idealFiniteAdeles J : Set (FiniteAdeleRing (𝓞 K) K))` using `fun a _ ↦ Set.mem_iUnion.2 (exists_mem_idealFiniteAdeles a)`. Establish `hdir : Directed (· ⊆ ·) fun J : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦ (idealFiniteAdeles J : Set (FiniteAdeleRing (𝓞 K) K))` using `fun I J ↦ ⟨fractionalIdealSupUnit I J, idealFiniteAdeles_subset le_sup_left, idealFiniteAdeles_subset le_sup_right⟩`. Conclude with `hC.elim_directed_cover _ (fun J ↦ isOpen_idealFiniteAdeles J) hcov hdir`.
-/
theorem exists_subset_idealFiniteAdeles {C : Set (FiniteAdeleRing (𝓞 K) K)} (hC : IsCompact C) :
    ∃ L : (FractionalIdeal (𝓞 K)⁰ K)ˣ, C ⊆ idealFiniteAdeles L := by
  have hcov : C ⊆ ⋃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (idealFiniteAdeles J : Set (FiniteAdeleRing (𝓞 K) K)) :=
    fun a _ ↦ Set.mem_iUnion.2 (exists_mem_idealFiniteAdeles a)
  have hdir : Directed (· ⊆ ·) fun J : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
      (idealFiniteAdeles J : Set (FiniteAdeleRing (𝓞 K) K)) := fun I J ↦
    ⟨fractionalIdealSupUnit I J, idealFiniteAdeles_subset le_sup_left, idealFiniteAdeles_subset le_sup_right⟩
  exact hC.elim_directed_cover _ (fun J ↦ isOpen_idealFiniteAdeles J) hcov hdir

end

end GroundTheory.Global
