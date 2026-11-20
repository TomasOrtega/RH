import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Metric

noncomputable section

namespace KShort

def cube (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| < c}

/- English proof (translation)
Use extensionality with `x`. Simplify using `[cube, abs_lt]`.
-/
theorem cube_eq (n : ℕ) (c : ℝ) :
    cube n c = (WithLp.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin n => Set.Ioo (-c) c) := by
  ext x; simp [cube, abs_lt]

/- English proof (translation)
Rewrite using `[cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]`. Simplify using `only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← ENNReal.ofReal_pow (by linarith)]`. Put the polynomial expressions in normal form.
-/
theorem volume_cube (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cube n c) = ENNReal.ofReal ((2 * c) ^ n) := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  ring_nf

/- English proof (translation)
Establish `hsn : 0 < √(n : ℝ)` using `Real.sqrt_pos.2 (by exact_mod_cast hn)`. Establish `hsq : (√(n : ℝ)) ^ 2 = n` using `Real.sq_sqrt (by positivity)`. Establish `h1 : ∀ i, x i ^ 2 < (lam / √n) ^ 2` using `fun i => by`. Use `hx i` as an intermediate fact. Establish `h0 : 0 ≤ |x i|` using `abs_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ∑ i, x i ^ 2 < ∑ _i : Fin n, (lam / √n) ^ 2` using `Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => h1 i`. Establish `hsum' : ∑ _i : Fin n, (lam / √n) ^ 2 = lam ^ 2`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_pow, hsq, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[EuclideanSpace.norm_eq]`. Rewrite using `[Real.sqrt_lt' hlam]`. Simplify `hsum` using `[Real.norm_eq_abs, sq_abs, hsum']`.
-/
theorem norm_lt_of_mem_cube {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube n (lam / √n)) : ‖x‖ < lam := by
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h1 : ∀ i, x i ^ 2 < (lam / √n) ^ 2 := fun i => by
    have := hx i
    have h0 : 0 ≤ |x i| := abs_nonneg _
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ < (lam / √n) ^ 2 := by gcongr
  have hsum : ∑ i, x i ^ 2 < ∑ _i : Fin n, (lam / √n) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => h1 i
  have hsum' : ∑ _i : Fin n, (lam / √n) ^ 2 = lam ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_pow, hsq, nsmul_eq_mul]
    field_simp
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_lt' hlam]
  simpa [Real.norm_eq_abs, sq_abs, hsum'] using hsum

/- English proof (translation)
Introduce `x hx y hy a b ha hb hab i`. Establish `hxi` using `hx i`. Establish `hyi` using `hy i`. Simplify using `only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Break down `ha.lt_or_eq with ha' | ha'` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Establish `: b * |y i| ≤ b * c` using `mul_le_mul_of_nonneg_left hyi.le hb`. Establish `: a * |x i| < a * c` using `mul_lt_mul_of_pos_left hxi ha'`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = c := by rw [← add_mul, hab, one_mul]`. Substitute `ha'` using the available equality. Simplify using `only [zero_add] at hab`. Substitute `hab` using the available equality. Simplify using `using hyi`.
-/
theorem convex_cube (n : ℕ) (c : ℝ) : Convex ℝ (cube n c) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < c := by
      rcases ha.lt_or_eq with ha' | ha'
      · calc a * |x i| + b * |y i| < a * c + b * c := by
              have : b * |y i| ≤ b * c := mul_le_mul_of_nonneg_left hyi.le hb
              have : a * |x i| < a * c := mul_lt_mul_of_pos_left hxi ha'
              linarith
          _ = c := by rw [← add_mul, hab, one_mul]
      · subst ha'
        simp only [zero_add] at hab
        subst hab
        simpa using hyi

end KShort

namespace KShort

variable {n : ℕ}

/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ L`. Use `set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)`. Establish `fund : IsAddFundamentalDomain L.toAddSubgroup F volume` using `ZLattice.isAddFundamentalDomain b volume`. Establish `hcov : ZLattice.covolume L = volume.real F` using `ZLattice.covolume_eq_measure_fundamentalDomain L volume fund`. Establish `hFfin : volume F ≠ ⊤` using `(Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _)).ne`.

Establish `hc : 0 ≤ lam / √n` using `by positivity`. Establish `hle : volume (cube n (lam / √n)) ≤ volume F * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n))`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `: Countable L.toAddSubgroup` using `(inferInstance : Countable L)`.

Establish `hsymm : ∀ y ∈ cube n (lam / √n), -y ∈ cube n (lam / √n)`. Introduce `y hy i`. Use `hy i` as an intermediate fact. Simplify `this` using `[abs_neg]`. Take `⟨x, hx0, hx⟩` from `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup) fund hsymm (convex_cube n _) hlt`.

Establish `h1` using `norm_lt_of_mem_cube hn hlam hx`. Establish `h2` using `hmin (x : EuclideanSpace ℝ (Fin n)) x.2 (by`. Introduce `h`. Apply `hx0` to reduce the goal to its premises. Conclude with `Subtype.ext h)`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hle` using `[volume_cube n hc, finrank_euclideanSpace, Fintype.card_fin]`. Rewrite `hle` using `[← ENNReal.ofReal_toReal hFfin]`. Rewrite using `[show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by`. Rewrite `hle` using `[ENNReal.ofReal_pow (by norm_num)]; simp]`.

Rewrite `hle` using `[← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Rewrite using `[hcov, measureReal_def]`. Establish `h2n : (0 : ℝ) < 2 ^ n` using `by positivity`. Rewrite `hle` using `[mul_pow]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pow_le_covolume (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (lam / √n) ^ n ≤ ZLattice.covolume L := by
  set b := Module.Free.chooseBasis ℤ L
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have fund : IsAddFundamentalDomain L.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hcov : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hFfin : volume F ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _)).ne
  have hc : 0 ≤ lam / √n := by positivity
  have hle : volume (cube n (lam / √n)) ≤ volume F * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    by_contra hlt
    push Not at hlt
    have : Countable L.toAddSubgroup := (inferInstance : Countable L)
    have hsymm : ∀ y ∈ cube n (lam / √n), -y ∈ cube n (lam / √n) := by
      intro y hy i
      have := hy i
      simpa [abs_neg] using this
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) fund hsymm (convex_cube n _) hlt
    have h1 := norm_lt_of_mem_cube hn hlam hx
    have h2 := hmin (x : EuclideanSpace ℝ (Fin n)) x.2 (by
      intro h; apply hx0; exact Subtype.ext h)
    linarith
  rw [volume_cube n hc, finrank_euclideanSpace, Fintype.card_fin] at hle
  rw [← ENNReal.ofReal_toReal hFfin] at hle
  rw [show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp] at hle
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  rw [hcov, measureReal_def]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_pow] at hle
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hbot : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Conclude with `h`.

Rewrite `hbot` using `[IsZLattice.span_top]`. Establish `: (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ∈ (⊥ : Submodule ℝ _)`. Rewrite using `[← hbot]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `this` using `[Submodule.mem_bot]`.

Use `congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) this` as an intermediate fact. Simplify using `at this`.
-/
theorem exists_ne_zero (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] : ∃ v ∈ L, v ≠ 0 := by
  by_contra h
  push Not at h
  have hbot : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact h
  rw [IsZLattice.span_top] at hbot
  have : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ∈ (⊥ : Submodule ℝ _) := by
    rw [← hbot]; trivial
  rw [Submodule.mem_bot] at this
  have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) this
  simp at this

/- English proof (translation)
Establish `h` using `Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : EuclideanSpace ℝ (Fin n)) r) (s := (L : Set (EuclideanSpace ℝ (Fin n)))) DiscreteTopology.isDiscrete isBounded_closedBall (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)`. Use `h.subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hr⟩`. Conclude with `⟨by simpa using hr, hv⟩`.
-/
theorem finite_ball (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] (r : ℝ) :
    {v | v ∈ L ∧ ‖v‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
    (s := (L : Set (EuclideanSpace ℝ (Fin n)))) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩

/- English proof (translation)
Take `⟨v₀, hv₀, hv₀0⟩` from `exists_ne_zero hn L`. Establish `hfin : {v | v ∈ L ∧ ‖v‖ ≤ ‖v₀‖ ∧ v ≠ 0}.Finite` using `(finite_ball L ‖v₀‖).subset fun v hv => ⟨hv.1, hv.2.1⟩`. Establish `hne : hfin.toFinset.Nonempty` using `⟨v₀, by simp [hv₀, hv₀0]⟩`. Take `⟨w, hw, hwmin⟩` from `hfin.toFinset.exists_min_image (fun v => ‖v‖) hne`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw hwmin`.

Use `⟨‖w‖, norm_pos_iff.2 hw.2.2, ⟨w, hw.1, hw.2.2, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨v, hv, hv0, rfl⟩`. Distinguish the cases in `h : ‖v‖ ≤ ‖v₀‖`. Conclude with `hwmin v ⟨hv, h, hv0⟩`. Use `push Not at h`.

Combine the linear relations using `[hw.2.1]`.
-/
theorem exists_isLeast (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ lam : ℝ, 0 < lam ∧ IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero hn L
  have hfin : {v | v ∈ L ∧ ‖v‖ ≤ ‖v₀‖ ∧ v ≠ 0}.Finite :=
    (finite_ball L ‖v₀‖).subset fun v hv => ⟨hv.1, hv.2.1⟩
  have hne : hfin.toFinset.Nonempty := ⟨v₀, by simp [hv₀, hv₀0]⟩
  obtain ⟨w, hw, hwmin⟩ := hfin.toFinset.exists_min_image (fun v => ‖v‖) hne
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw hwmin
  refine ⟨‖w‖, norm_pos_iff.2 hw.2.2, ⟨w, hw.1, hw.2.2, rfl⟩, ?_⟩
  rintro t ⟨v, hv, hv0, rfl⟩
  by_cases h : ‖v‖ ≤ ‖v₀‖
  · exact hwmin v ⟨hv, h, hv0⟩
  · push Not at h
    linarith [hw.2.1]

end KShort

namespace KShort

variable {n : ℕ}

/- English proof (translation)
Set `_ : MeasurableSpace U` to `borel U`. Establish `: BorelSpace U` using `⟨rfl⟩`. Use `set μ : Measure U := (Module.finBasis ℝ U).addHaar with hμ`. Use `set a := finrank ℝ U with ha`. Use `set T : Set U := {w | (w : EuclideanSpace ℝ (Fin n)) ∈ L ∧ ‖w‖ ≤ r} with hT`.

Establish `hTfin : T.Finite` using `((finite_ball L r).preimage Subtype.val_injective.injOn).subset fun w hw => ⟨hw.1, hw.2⟩`. Establish `himage : Subtype.val '' T = {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r}`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `⟨hw.1, w.2, hw.2⟩`. Introduce and unpack `⟨hL, hU, hr'⟩`. Conclude with `⟨⟨v, hU⟩, ⟨hL, hr'⟩, rfl⟩`. Rewrite using `[← himage, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_eq_toFinset_card T hTfin]`. Use `set s := hTfin.toFinset with hs`.

Establish `hl2 : 0 < lam / 2` using `half_pos hlam`. Establish `hdisj : Set.PairwiseDisjoint (s : Set U) fun w => ball w (lam / 2)`. Introduce `w hw w' hw' hne`. Apply `ball_disjoint_ball` to reduce the goal to its premises. Rewrite using `[add_halves, dist_eq_norm]`.

Establish `hw1 : (w : EuclideanSpace ℝ (Fin n)) ∈ L`. Simplify `(Set.Finite.mem_toFinset hTfin).1 hw |>.1` using `[hs, hT]`. Establish `hw2 : (w' : EuclideanSpace ℝ (Fin n)) ∈ L`. Simplify `(Set.Finite.mem_toFinset hTfin).1 hw' |>.1` using `[hs, hT]`. Establish `hsub : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ∈ L`.

Rewrite using `[Submodule.coe_sub]`. Conclude with `L.sub_mem hw1 hw2`. Establish `hne0 : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Establish `: w - w' = 0` using `Subtype.ext h`. Conclude with `sub_eq_zero.1 this`. Use `hmin _ hsub hne0` as an intermediate fact. Simplify using `using this`. Establish `hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : U) (r + lam / 2)`.

Introduce `x hx`. Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨w, hw, hxw⟩` from `hx`. Establish `hwr : ‖w‖ ≤ r` using `((Set.Finite.mem_toFinset hTfin).1 hw).2`. Rewrite using `[mem_ball_zero_iff]`.

Rewrite `hxw` using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Use `_ < r + lam / 2 := by linarith`.

Establish `hmeas` using `measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball`. Establish `hle` using `measure_mono (μ := μ) hsubset`. Rewrite `hle` using `[hmeas]`. Simplify using `only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle`. Rewrite `hle` using `[Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)]`.

Establish `hc0 : μ (ball 0 1) ≠ 0` using `(measure_ball_pos μ 0 one_pos).ne'`. Establish `hct : μ (ball 0 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite `hle` using `[← mul_assoc]`. Establish `hle'` using `(ENNReal.mul_le_mul_iff_left hc0 hct).1 hle`. Rewrite `hle'` using `[show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)]`.

Establish `hpos : 0 < (lam / 2) ^ a` using `by positivity`. Establish `hcard : (s.card : ℝ) ≤ ((r + lam / 2) / (lam / 2)) ^ a`. Rewrite using `[div_pow, le_div_iff₀ hpos]`. Conclude with `hle'`. Use `hcard.trans (pow_le_pow_left₀ (div_nonneg (by linarith) hl2.le) ?_ a)` and prove the remaining obligations.

Rewrite using `[div_le_div_iff₀ hl2 hlam]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem card_le (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {lam r : ℝ} (hlam : 0 < lam) (hr : lam ≤ r)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ finrank ℝ U := by
  classical
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  set μ : Measure U := (Module.finBasis ℝ U).addHaar with hμ
  set a := finrank ℝ U with ha
  set T : Set U := {w | (w : EuclideanSpace ℝ (Fin n)) ∈ L ∧ ‖w‖ ≤ r} with hT
  have hTfin : T.Finite :=
    ((finite_ball L r).preimage Subtype.val_injective.injOn).subset fun w hw => ⟨hw.1, hw.2⟩
  have himage : Subtype.val '' T = {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, w.2, hw.2⟩
    · rintro ⟨hL, hU, hr'⟩
      exact ⟨⟨v, hU⟩, ⟨hL, hr'⟩, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_eq_toFinset_card T hTfin]
  set s := hTfin.toFinset with hs
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set U) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    have hw1 : (w : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw |>.1
    have hw2 : (w' : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw' |>.1
    have hsub : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ∈ L := by
      rw [Submodule.coe_sub]; exact L.sub_mem hw1 hw2
    have hne0 : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      apply hne
      have : w - w' = 0 := Subtype.ext h
      exact sub_eq_zero.1 this
    have := hmin _ hsub hne0
    simpa using this
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : U) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    have hwr : ‖w‖ ≤ r := ((Set.Finite.mem_toFinset hTfin).1 hw).2
    rw [mem_ball_zero_iff]
    rw [mem_ball] at hxw
    calc ‖x‖ ≤ ‖w‖ + dist x w := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖w + (x - w)‖ := by abel_nf
            _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ a := by positivity
  have hcard : (s.card : ℝ) ≤ ((r + lam / 2) / (lam / 2)) ^ a := by
    rw [div_pow, le_div_iff₀ hpos]; exact hle'
  refine hcard.trans (pow_le_pow_left₀ (div_nonneg (by linarith) hl2.le) ?_ a)
  rw [div_le_div_iff₀ hl2 hlam]
  nlinarith

end KShort

/- English proof (translation)
Introduce `n hn L _ _`. Take `⟨lam, hlam, hleast⟩` from `KShort.exists_isLeast hn L`. Establish `hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖` using `fun v hv hv0 => hleast.2 ⟨v, hv, hv0, rfl⟩`. Use `⟨lam, hleast, KShort.pow_le_covolume hn L hlam hmin, ?_⟩` and prove the remaining obligations. Introduce `U r hr`.

Establish `hfin : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite` using `(KShort.finite_ball L r).subset fun v hv => ⟨hv.1, hv.2.2.1⟩`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hcard` using `KShort.card_le L U hlam hr hmin`. Establish `heq : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} = insert 0 {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}`. Use extensionality with `v`.

Distinguish the cases in `h : v = 0`. Substitute `h` using the available equality. Simplify using `only [Set.mem_ofPred_eq, Set.mem_insert_iff, true_or, iff_true]`. Conclude with `⟨L.zero_mem, U.zero_mem, by simp; linarith⟩`. Simplify using `[h]`.

Rewrite `hcard` using `[heq, Set.ncard_insert_of_notMem (by simp) hfin]`. Move the coercions through the operations in `at hcard`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ShortVectors.intersectionNumber_baseChange : ShortVectors.Statement := by
  intro n hn L _ _
  obtain ⟨lam, hlam, hleast⟩ := KShort.exists_isLeast hn L
  have hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := fun v hv hv0 => hleast.2 ⟨v, hv, hv0, rfl⟩
  refine ⟨lam, hleast, KShort.pow_le_covolume hn L hlam hmin, ?_⟩
  intro U r hr
  have hfin : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite :=
    (KShort.finite_ball L r).subset fun v hv => ⟨hv.1, hv.2.2.1⟩
  refine ⟨hfin, ?_⟩
  have hcard := KShort.card_le L U hlam hr hmin
  have heq : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} =
      insert 0 {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0} := by
    ext v
    by_cases h : v = 0
    · subst h
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, true_or, iff_true]
      exact ⟨L.zero_mem, U.zero_mem, by simp; linarith⟩
    · simp [h]
  rw [heq, Set.ncard_insert_of_notMem (by simp) hfin] at hcard
  push_cast at hcard
  linarith

end

end GroundTheory.Heights₂.Heights
