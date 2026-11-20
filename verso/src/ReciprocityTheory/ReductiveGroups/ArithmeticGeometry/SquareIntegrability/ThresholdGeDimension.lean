import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField MeasureTheory
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace Col

/- English proof (translation)
Use `haveI : VAddInvariantMeasure (↥(Submodule.span ℤ (Set.range b))) (EuclideanSpace ℂ ι) volume := ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩`. Establish `hfd` using `ZSpan.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℂ ι))`. Establish `ht` using `hfd.preimage_of_equiv (measurePreserving_sub_right volume a).quasiMeasurePreserving (e := id) Function.bijective_id (fun g x => add_sub_assoc (g : EuclideanSpace ℂ ι) x a)`. Establish `hpre : (fun x => x + a) ⁻¹' ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b) = ZSpan.fundamentalDomain b`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h1` using `(measurePreserving_add_right (volume : Measure (EuclideanSpace ℂ ι)) a).setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding F ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b)`. Rewrite `h1` using `[hpre]`. Use `Eq.trans h1 (ht.setLIntegral_eq hfd F fun g x => ?_)` and prove the remaining obligations. Use `show F ((g : EuclideanSpace ℂ ι) + x) = F x`.

Rewrite using `[add_comm]`. Conclude with `hF _ g.2 x`.
-/
theorem lint_fd_shift {ι : Type} [Fintype ι] {κ : Type} [Finite κ]
    (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (F : EuclideanSpace ℂ ι → ℝ≥0∞)
    (hF : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ x, F (x + γ) = F x) (a : EuclideanSpace ℂ ι) :
    ∫⁻ x in ZSpan.fundamentalDomain b, F (x + a) = ∫⁻ x in ZSpan.fundamentalDomain b, F x := by
  haveI : VAddInvariantMeasure (↥(Submodule.span ℤ (Set.range b))) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have hfd := ZSpan.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℂ ι))
  have ht := hfd.preimage_of_equiv (measurePreserving_sub_right volume a).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g x => add_sub_assoc (g : EuclideanSpace ℂ ι) x a)
  have hpre : (fun x => x + a) ⁻¹' ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b) =
      ZSpan.fundamentalDomain b := by
    ext x; simp
  have h1 := (measurePreserving_add_right (volume : Measure (EuclideanSpace ℂ ι)) a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding F ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b)
  rw [hpre] at h1
  refine Eq.trans h1 (ht.setLIntegral_eq hfd F fun g x => ?_)
  show F ((g : EuclideanSpace ℂ ι) + x) = F x
  rw [add_comm]
  exact hF _ g.2 x

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)`. Evaluate the numerical expressions using `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem three_le_exp : (3 : ℝ) ≤ Real.exp (3 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  norm_num at h
  linarith

/- English proof (translation)
Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hx0 : 0 ≤ x` using `by linarith`. Establish `hpi : 3 < Real.pi` using `Real.pi_gt_three`. Establish `h1 : 3 / 2 * (n : ℝ) + 9 / 4 ≤ Real.pi / 4 * x`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hpi.le) hx0]`.

Establish `h2 : (3 : ℝ) ^ n ≤ Real.exp (3 / 2 * n)`. Rewrite using `[show (3 / 2 * (n : ℝ)) = n * (3 / 2) by ring, Real.exp_nat_mul]`. Establish `h3e` using `three_le_exp`. Use `gcongr`. Establish `h3 : (2 : ℝ) ≤ Real.exp (9 / 4)` using `by linarith [Real.add_one_le_exp (9 / 4 : ℝ)]`.

Establish `h4 : Real.exp (3 / 2 * n) * Real.exp (9 / 4) ≤ Real.exp (Real.pi / 4 * x)`. Rewrite using `[← Real.exp_add]`. Conclude with `Real.exp_le_exp.2 h1`. Establish `h5 : Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) = 1`. Rewrite using `[← Real.exp_add]`.

Simplify using the standard rewrite rules. Establish `hpos` using `Real.exp_pos (-(Real.pi / 4 * x))`. Establish `h6 : 2 * 3 ^ n ≤ Real.exp (Real.pi / 4 * x)`. Use `mul_le_mul h2 h3 (by norm_num) (Real.exp_pos _).le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem num1 (n : ℕ) (x : ℝ) (hx : 2 * (n : ℝ) + 3 ≤ x) :
    2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h1 : 3 / 2 * (n : ℝ) + 9 / 4 ≤ Real.pi / 4 * x := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpi.le) hx0]
  have h2 : (3 : ℝ) ^ n ≤ Real.exp (3 / 2 * n) := by
    rw [show (3 / 2 * (n : ℝ)) = n * (3 / 2) by ring, Real.exp_nat_mul]
    have h3e := three_le_exp
    gcongr
  have h3 : (2 : ℝ) ≤ Real.exp (9 / 4) := by linarith [Real.add_one_le_exp (9 / 4 : ℝ)]
  have h4 : Real.exp (3 / 2 * n) * Real.exp (9 / 4) ≤ Real.exp (Real.pi / 4 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
  have h5 : Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(Real.pi / 4 * x))
  have h6 : 2 * 3 ^ n ≤ Real.exp (Real.pi / 4 * x) := by
    have := mul_le_mul h2 h3 (by norm_num) (Real.exp_pos _).le
    linarith
  calc 2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) :=
        mul_le_mul_of_nonneg_right h6 hpos.le
    _ = 1 := h5

section Wsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

/- English proof (translation)
Take `⟨ρ, hρ, hr⟩` from `hI.rank`. Establish `h6 : (X.gA : ℝ) * Real.log 2 + 2 * dstar (E` using `E) P.m + 3 + (DF + 1) * (X.r * Real.log X.r + 3 * X.r + 3) ≤ P.q * b0 (E := E) P.q P.R0 := P.C6`. Establish `hdK : (dK (IR I) : ℝ) ≤ dstar (E` using `E) P.m := by`. Establish `h : Module.finrank ℝ (IR I) ≤ 2 * PT.f E * P.m`. Rewrite using `[hr]`.

Conclude with `Nat.mul_le_mul_left _ hρ`. Conclude with `h` after adjusting the coercions. Establish `hlog : 0 ≤ (X.r : ℝ) * Real.log X.r` using `mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hg : (0 : ℝ) ≤ X.gA * Real.log 2` using `mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)`. Establish `hr0 : (0 : ℝ) ≤ X.r` using `Nat.cast_nonneg _`.

Establish `hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3)` using `mul_nonneg (by positivity) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem threshold_ge_dimension : 2 * (dK (IR I) : ℝ) + 3 ≤ P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρ, hr⟩ := hI.rank
  have h6 : (X.gA : ℝ) * Real.log 2 + 2 * dstar (E := E) P.m + 3 +
      (DF + 1) * (X.r * Real.log X.r + 3 * X.r + 3) ≤ P.q * b0 (E := E) P.q P.R0 := P.C6
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    have h : Module.finrank ℝ (IR I) ≤ 2 * PT.f E * P.m := by
      rw [hr]; exact Nat.mul_le_mul_left _ hρ
    exact_mod_cast h
  have hlog : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hg : (0 : ℝ) ≤ X.gA * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hinf`. Establish `hb` using `cutoff_pos P`. Use `set δ := Real.sqrt (b0 (E := E) P.q P.R0)`. Establish `hδ : 0 < δ` using `Real.sqrt_pos.2 hb`. Use `set R' := max R δ`.

Take `⟨N, hN⟩` from `exists_nat_gt ((3 * R' / δ) ^ (dK (IR I)))`. Take `⟨T, hT, hTc⟩` from `Set.Infinite.exists_subset_card_eq hinf N`. Establish `hinj : Set.InjOn (uQ X I) T`. Introduce `c _ c' _ h`. Assume the negation of the conclusion as `hne`.

Use `uQ_dist hI hne` as an intermediate fact. Rewrite `this` using `[h, dist_self]`. Conclude with `absurd this (not_le.2 hδ)`. Use `pack_K hP (IR I) (T.image (uQ X I)) (fun u hu => by obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu; exact uQ_mem c) δ R' hδ (le_max_right _ _) (fun u hu => by` as an intermediate fact. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hu`.

Conclude with `(hT hc).trans (le_max_left _ _))`. Use the proof step `(fun u hu u' hu' hne => by`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hu`. Take `⟨c', -, rfl⟩` from `Finset.mem_image.1 hu'`. Conclude with `uQ_dist hI (fun h => hne (by rw [h])))`.

Rewrite `this` using `[Finset.card_image_of_injOn hinj, hTc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem finite_uQ (hP : Ext.PackingCount) (R : ℝ) : {c : Qc X I | ‖uQ X I c‖ ≤ R}.Finite := by
  classical
  by_contra hinf
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  set R' := max R δ
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R' / δ) ^ (dK (IR I)))
  obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hinj : Set.InjOn (uQ X I) T := by
    intro c _ c' _ h
    by_contra hne
    have := uQ_dist hI hne
    rw [h, dist_self] at this
    exact absurd this (not_le.2 hδ)
  have := pack_K hP (IR I) (T.image (uQ X I))
    (fun u hu => by obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu; exact uQ_mem c) δ R' hδ
    (le_max_right _ _)
    (fun u hu => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
      exact (hT hc).trans (le_max_left _ _))
    (fun u hu u' hu' hne => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hu'
      exact uQ_dist hI (fun h => hne (by rw [h])))
  rw [Finset.card_image_of_injOn hinj, hTc] at this
  linarith

end Wsec

/- English proof (translation)
Establish `key : ∀ t : ℝ, 0 ≤ (∑' c, w c) * t * t + (-2 * ∑' c, w c * N c) * t + ∑' c, w c * N c ^ 2`. Introduce `t`. Establish `e : ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) = (∑' c, w c * N c ^ 2) - 2 * t * (∑' c, w c * N c) + t ^ 2 * ∑' c, w c`. Rewrite using `[(h2.sub (h3.mul_left _)).tsum_add (h1.mul_left _), h2.tsum_sub (h3.mul_left _), tsum_mul_left, tsum_mul_left]`. Establish `hnn : 0 ≤ ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c)` using `tsum_nonneg fun c => by nlinarith [mul_nonneg (hw c) (sq_nonneg (N c - t))]`.

Use polynomial arithmetic with `[e, hnn]`. Establish `hd` using `discrim_le_zero (a := ∑' c, w c) (b := -2 * ∑' c, w c * N c) (c := ∑' c, w c * N c ^ 2) (fun t => by nlinarith [key t])`. Unfold `discrim at hd`. Use polynomial arithmetic with `[hd]`.
-/
theorem cs_tsum {κ : Type} (w N : κ → ℝ) (hw : ∀ c, 0 ≤ w c) (hN : ∀ c, 0 ≤ N c) (h1 : Summable w)
    (h2 : Summable (fun c => w c * N c ^ 2)) (h3 : Summable (fun c => w c * N c)) :
    (∑' c, w c * N c) ^ 2 ≤ (∑' c, w c) * ∑' c, w c * N c ^ 2 := by
  have key : ∀ t : ℝ, 0 ≤ (∑' c, w c) * t * t + (-2 * ∑' c, w c * N c) * t + ∑' c, w c * N c ^ 2 := by
    intro t
    have e : ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) =
        (∑' c, w c * N c ^ 2) - 2 * t * (∑' c, w c * N c) + t ^ 2 * ∑' c, w c := by
      rw [(h2.sub (h3.mul_left _)).tsum_add (h1.mul_left _), h2.tsum_sub (h3.mul_left _), tsum_mul_left,
        tsum_mul_left]
    have hnn : 0 ≤ ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) :=
      tsum_nonneg fun c => by nlinarith [mul_nonneg (hw c) (sq_nonneg (N c - t))]
    nlinarith [e, hnn]
  have hd := discrim_le_zero (a := ∑' c, w c) (b := -2 * ∑' c, w c * N c) (c := ∑' c, w c * N c ^ 2)
    (fun t => by nlinarith [key t])
  unfold discrim at hd
  nlinarith [hd]

section Wsec2

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
include hI hP hA

/- English proof (translation)
Establish `hpi` using `Real.pi_gt_three`. Use `set g : Qc X I → ℝ := fun c => Real.exp (-(Real.pi / 4 * P.q) * ‖uQ X I c‖ ^ 2) with hg`. Establish `hgs : Summable g` using `summable_gauss hI hP hA (Real.pi / 4) (by linarith)`. Establish `htail` using `tailQ hI hP hA (Real.pi / 4) (by positivity) (cond_tail hI (Real.pi / 4) (by linarith))`. Establish `hsplit : ∑' c, g c = g 0 + ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, g c`.

Rewrite using `[← hgs.sum_add_tsum_compl (s := {0}), Finset.sum_singleton]`. Both sides reduce to the same expression. Establish `hg0 : g 0 = 1` using `by simp [hg]`. Establish `hnum` using `num1 (dK (IR I)) (P.q * b0 (E := E) P.q P.R0) (threshold_ge_dimension hI)`. Establish `hgle : ∑' c, g c ≤ 2`.

Rewrite using `[hsplit, hg0]`. Establish `h2` using `htail.2`. Rewrite `h2` using `[show Real.pi / 4 * P.q * b0 (E := E) P.q P.R0 = Real.pi / 4 * (P.q * b0 (E := E) P.q P.R0) by ring]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨c0, -, hmin⟩` from `Set.exists_min_image {c : Qc X I | ‖uQ X I c‖ ≤ 2 * ‖u‖} (fun c => ‖u - uQ X I c‖) (finite_uQ hI hP _) ⟨0, by simp⟩`.

Establish `hglob : ∀ c, ‖u - uQ X I c0‖ ≤ ‖u - uQ X I c‖`. Introduce `c`. Distinguish the cases in `hc : ‖uQ X I c‖ ≤ 2 * ‖u‖`. Conclude with `hmin c hc`. Establish `h0` using `hmin 0 (by simp)`.

Simplify using `only [map_zero, sub_zero] at h0`. Use `push Not at hc`. Establish `: ‖uQ X I c‖ - ‖u‖ ≤ ‖u - uQ X I c‖`. Use `norm_sub_norm_le (uQ X I c) u` as an intermediate fact. Rewrite `this` using `[norm_sub_rev]`.

Conclude with `this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ∀ c, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ g (c - c0)`. Introduce `c`. Simplify using `only [hg, map_sub]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h1 : ‖uQ X I c - uQ X I c0‖ ≤ 2 * ‖u - uQ X I c‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖uQ X I c - uQ X I c0‖ ^ 2 ≤ 4 * ‖u - uQ X I c‖ ^ 2`. Use polynomial arithmetic with `[norm_nonneg (uQ X I c - uQ X I c0), norm_nonneg (u - uQ X I c)]`.

Establish `hq : (0 : ℝ) ≤ P.q` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Real.pi / 4 * P.q)]`. Establish `hgs' : Summable (fun c => g (c - c0))` using `(Equiv.subRight c0).summable_iff.2 hgs`. Establish `hs : Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2))` using `Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpt hgs'`. Use `⟨hs, (hs.tsum_le_tsum hpt hgs').trans ?_⟩` and prove the remaining obligations.

Use `(Equiv.subRight c0).tsum_eq g` as an intermediate fact. Simplify using `only [Equiv.subRight_apply] at this`. Rewrite using `[this]`. Conclude with `hgle`.
-/
theorem sum_w_le (u : Vsp X.dim) :
    Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) ∧
      ∑' c : Qc X I, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ 2 := by
  have hpi := Real.pi_gt_three
  set g : Qc X I → ℝ := fun c => Real.exp (-(Real.pi / 4 * P.q) * ‖uQ X I c‖ ^ 2) with hg
  have hgs : Summable g := summable_gauss hI hP hA (Real.pi / 4) (by linarith)
  have htail := tailQ hI hP hA (Real.pi / 4) (by positivity) (cond_tail hI (Real.pi / 4) (by linarith))
  have hsplit : ∑' c, g c = g 0 + ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, g c := by
    rw [← hgs.sum_add_tsum_compl (s := {0}), Finset.sum_singleton]
    rfl
  have hg0 : g 0 = 1 := by simp [hg]
  have hnum := num1 (dK (IR I)) (P.q * b0 (E := E) P.q P.R0) (threshold_ge_dimension hI)
  have hgle : ∑' c, g c ≤ 2 := by
    rw [hsplit, hg0]
    have h2 := htail.2
    rw [show Real.pi / 4 * P.q * b0 (E := E) P.q P.R0 = Real.pi / 4 * (P.q * b0 (E := E) P.q P.R0) by ring] at h2
    linarith
  obtain ⟨c0, -, hmin⟩ := Set.exists_min_image {c : Qc X I | ‖uQ X I c‖ ≤ 2 * ‖u‖}
    (fun c => ‖u - uQ X I c‖) (finite_uQ hI hP _) ⟨0, by simp⟩
  have hglob : ∀ c, ‖u - uQ X I c0‖ ≤ ‖u - uQ X I c‖ := by
    intro c
    by_cases hc : ‖uQ X I c‖ ≤ 2 * ‖u‖
    · exact hmin c hc
    · have h0 := hmin 0 (by simp)
      simp only [map_zero, sub_zero] at h0
      push Not at hc
      have : ‖uQ X I c‖ - ‖u‖ ≤ ‖u - uQ X I c‖ := by
        have := norm_sub_norm_le (uQ X I c) u
        rw [norm_sub_rev] at this; exact this
      linarith
  have hpt : ∀ c, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ g (c - c0) := by
    intro c
    simp only [hg, map_sub]
    apply Real.exp_le_exp.2
    have h1 : ‖uQ X I c - uQ X I c0‖ ≤ 2 * ‖u - uQ X I c‖ := by
      calc ‖uQ X I c - uQ X I c0‖ = ‖(u - uQ X I c0) - (u - uQ X I c)‖ := by congr 1; abel
        _ ≤ ‖u - uQ X I c0‖ + ‖u - uQ X I c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hglob c]
    have h2 : ‖uQ X I c - uQ X I c0‖ ^ 2 ≤ 4 * ‖u - uQ X I c‖ ^ 2 := by
      nlinarith [norm_nonneg (uQ X I c - uQ X I c0), norm_nonneg (u - uQ X I c)]
    have hq : (0 : ℝ) ≤ P.q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Real.pi / 4 * P.q)]
  have hgs' : Summable (fun c => g (c - c0)) := (Equiv.subRight c0).summable_iff.2 hgs
  have hs : Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpt hgs'
  refine ⟨hs, (hs.tsum_le_tsum hpt hgs').trans ?_⟩
  have := (Equiv.subRight c0).tsum_eq g
  simp only [Equiv.subRight_apply] at this
  rw [this]
  exact hgle

end Wsec2

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
