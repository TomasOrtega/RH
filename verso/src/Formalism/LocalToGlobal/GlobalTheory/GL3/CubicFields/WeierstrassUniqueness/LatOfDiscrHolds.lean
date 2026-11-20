import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

/- English proof (translation)
Establish `hk2 : 1 < 2 * k` using `by omega`. Establish `hsR : Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ (2 * k)` using `Real.summable_one_div_int_pow.mpr hk2`. Establish `hs : Summable fun n : ℤ ↦ 1 / (n : ℂ) ^ (2 * k)`. Use `(Complex.summable_ofReal).mpr hsR` as an intermediate fact. Use `this.congr fun n => ?_` and prove the remaining obligations.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[← tsum_nat_add_neg_add_one hs]`. Establish `hN : Summable fun n : ℕ ↦ 1 / (n : ℂ) ^ (2 * k)`. Use `hs.comp_injective Nat.cast_injective` as an intermediate fact.

Use `this.congr fun n => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hN1 : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ (2 * k)`. Use `(summable_nat_add_iff 1).mpr hN` as an intermediate fact. Use `this.congr fun n => ?_` and prove the remaining obligations.

Use `push_cast`. Both sides reduce to the same expression. Establish `e : ∀ n : ℕ, 1 / (((n : ℤ) : ℂ)) ^ (2 * k) + 1 / (((-(n + 1) : ℤ)) : ℂ) ^ (2 * k) = 1 / (n : ℂ) ^ (2 * k) + 1 / ((n : ℂ) + 1) ^ (2 * k)`. Introduce `n`. Use `push_cast`.

Rewrite using `[(even_two_mul k).neg_pow]`. Rewrite using `[tsum_congr e, hN.tsum_add hN1]`. Establish `h0 : ∑' n : ℕ, 1 / (n : ℂ) ^ (2 * k) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * k)`. Rewrite using `[hN.tsum_eq_zero_add]`. Establish `hz : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ (2 * k) = 0` using `by simp; omega`.

Rewrite using `[hz, zero_add]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hz` using `zeta_nat_eq_tsum_of_gt_one hk2`. Move the coercions through the operations in `at hz`.

Rewrite using `[← h0, ← hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_tsum_int (k : ℕ) (hk : 1 ≤ k) :
    ∑' n : ℤ, 1 / (n : ℂ) ^ (2 * k) = 2 * riemannZeta (2 * k) := by
  have hk2 : 1 < 2 * k := by omega
  have hsR : Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ (2 * k) := Real.summable_one_div_int_pow.mpr hk2
  have hs : Summable fun n : ℤ ↦ 1 / (n : ℂ) ^ (2 * k) := by
    have := (Complex.summable_ofReal).mpr hsR
    refine this.congr fun n => ?_
    push_cast; rfl
  rw [← tsum_nat_add_neg_add_one hs]
  have hN : Summable fun n : ℕ ↦ 1 / (n : ℂ) ^ (2 * k) := by
    have := hs.comp_injective Nat.cast_injective
    refine this.congr fun n => ?_
    simp
  have hN1 : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    have := (summable_nat_add_iff 1).mpr hN
    refine this.congr fun n => ?_
    push_cast; rfl
  have e : ∀ n : ℕ, 1 / (((n : ℤ) : ℂ)) ^ (2 * k) + 1 / (((-(n + 1) : ℤ)) : ℂ) ^ (2 * k)
      = 1 / (n : ℂ) ^ (2 * k) + 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    intro n; push_cast; rw [(even_two_mul k).neg_pow]
  rw [tsum_congr e, hN.tsum_add hN1]
  have h0 : ∑' n : ℕ, 1 / (n : ℂ) ^ (2 * k) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * k) := by
    rw [hN.tsum_eq_zero_add]
    have hz : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ (2 * k) = 0 := by simp; omega
    rw [hz, zero_add]
    push_cast; rfl
  have hz := zeta_nat_eq_tsum_of_gt_one hk2
  push_cast at hz
  rw [← h0, ← hz]; ring

/- English proof (translation)
Unfold `Formalism.MainNotions.TaylorLogMetric.eisG`. Set `f : {n : ℤ | n ≠ 0} → {w : ℂ // w ∈ AddSubgroup.zmultiples v ∧ w ≠ 0}` to `fun n => ⟨(n : ℂ) * v, ⟨n, by simp [zsmul_eq_mul]⟩, mul_ne_zero (by exact_mod_cast n.2) hv⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`.

Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `only [f, mul_left_inj' hv, Int.cast_inj] at this`. Conclude with `Subtype.ext this`. Introduce and unpack `⟨w, ⟨n, rfl⟩, hw⟩`. Use `⟨⟨n, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `at hw`. Simplify using `[f, zsmul_eq_mul]`. Rewrite using `[← (Equiv.ofBijective f hf).tsum_eq]`. Simplify using `only [Equiv.ofBijective_apply, f]`.

Establish `hc : ∀ n : {n : ℤ | n ≠ 0}, 1 / ((n : ℂ) * v) ^ (2 * k) = (1 / v ^ (2 * k)) * (1 / ((n : ℤ) : ℂ) ^ (2 * k))`. Introduce `n`. Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[tsum_congr hc, tsum_mul_left, tsum_subtype_eq_of_support_subset (f := fun n : ℤ => 1 / (n : ℂ) ^ (2 * k)) ?_, dg_tsum_int k hk]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `n hn`. Simplify using `only [Function.mem_support] at hn`. Simplify using `only [Set.mem_ofPred_eq]`. Introduce and unpack `rfl`.

Simplify using `at hn`. Use linear arithmetic over natural numbers and integers.
-/
theorem dg_eisG_cyc (v : ℂ) (hv : v ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Formalism.MainNotions.TaylorLogMetric.eisG (AddSubgroup.zmultiples v) k = 2 * riemannZeta (2 * k) / v ^ (2 * k) := by
  unfold Formalism.MainNotions.TaylorLogMetric.eisG
  let f : {n : ℤ | n ≠ 0} → {w : ℂ // w ∈ AddSubgroup.zmultiples v ∧ w ≠ 0} := fun n =>
    ⟨(n : ℂ) * v, ⟨n, by simp [zsmul_eq_mul]⟩, mul_ne_zero (by exact_mod_cast n.2) hv⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      simp only [f, mul_left_inj' hv, Int.cast_inj] at this
      exact Subtype.ext this
    · rintro ⟨w, ⟨n, rfl⟩, hw⟩
      refine ⟨⟨n, ?_⟩, ?_⟩
      · rintro rfl; simp at hw
      · simp [f, zsmul_eq_mul]
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  simp only [Equiv.ofBijective_apply, f]
  have hc : ∀ n : {n : ℤ | n ≠ 0}, 1 / ((n : ℂ) * v) ^ (2 * k)
      = (1 / v ^ (2 * k)) * (1 / ((n : ℤ) : ℂ) ^ (2 * k)) := by
    intro n; rw [mul_pow]; field_simp
  rw [tsum_congr hc, tsum_mul_left,
    tsum_subtype_eq_of_support_subset (f := fun n : ℤ => 1 / (n : ℂ) ^ (2 * k)) ?_, dg_tsum_int k hk]
  · ring
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    rintro rfl; simp at hn; omega

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Establish `h : ∀ k, Formalism.MainNotions.TaylorLogMetric.eisG (AddSubgroup.zmultiples (0 : ℂ)) k = 0`. Introduce `k`. Unfold `Formalism.MainNotions.TaylorLogMetric.eisG`.

Establish `: IsEmpty {w : ℂ // w ∈ AddSubgroup.zmultiples (0 : ℂ) ∧ w ≠ 0}` using `⟨fun w => w.2.2 (by simpa using w.2.1)⟩`. Conclude with `tsum_empty`. Simplify using `only [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h]`. Evaluate the numerical expressions. Unfold `Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3`.

Rewrite using `[dg_eisG_cyc v hv 2 (by norm_num), dg_eisG_cyc v hv 3 (by norm_num)]`. Use `push_cast`. Rewrite using `[show (2 : ℂ) * 2 = 4 by norm_num, show (2 : ℂ) * 3 = 6 by norm_num, riemannZeta_four, jac_riemannZeta_six]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dg_discr_cyc (v : ℂ) : Formalism.MainNotions.TaylorLogMetric.discr (AddSubgroup.zmultiples v) = 0 := by
  by_cases hv : v = 0
  · subst hv
    have h : ∀ k, Formalism.MainNotions.TaylorLogMetric.eisG (AddSubgroup.zmultiples (0 : ℂ)) k = 0 := by
      intro k
      unfold Formalism.MainNotions.TaylorLogMetric.eisG
      have : IsEmpty {w : ℂ // w ∈ AddSubgroup.zmultiples (0 : ℂ) ∧ w ≠ 0} :=
        ⟨fun w => w.2.2 (by simpa using w.2.1)⟩
      exact tsum_empty
    simp only [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h]
    norm_num
  · unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [dg_eisG_cyc v hv 2 (by norm_num), dg_eisG_cyc v hv 3 (by norm_num)]
    push_cast
    rw [show (2 : ℂ) * 2 = 4 by norm_num, show (2 : ℂ) * 3 = 6 by norm_num, riemannZeta_four,
      jac_riemannZeta_six]
    field_simp
    ring

/- English proof (translation)
Establish `hsum : ∃ k : ℕ, 1 ≤ k ∧ Summable (fun w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k))`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Apply `h` to reduce the goal to its premises. Establish `h2 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 2 = 0` using `tsum_eq_zero_of_not_summable (hn 2 (by norm_num))`.

Establish `h3 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 3 = 0` using `tsum_eq_zero_of_not_summable (hn 3 (by norm_num))`. Simplify using `[Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h2, h3]`. Take `⟨k, hk, hs⟩` from `hsum`. Establish `hfin : Set.Finite {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖}`. Use `hs.tendsto_cofinite_zero (Metric.ball_mem_nhds (0 : ℂ) one_pos)` as an intermediate fact.

Use `(Filter.mem_cofinite.mp this).subset ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Set.mem_ofPred_eq] at hw`. Simplify using `only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right, not_lt]`. Conclude with `hw`.

Use `set F : Set ℂ := Subtype.val '' {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖}`. Establish `hF : F.Finite` using `hfin.image _`. Establish `h0 : (0 : ℂ) ∈ Fᶜ`. Introduce and unpack `⟨w, _, hw⟩`. Conclude with `w.2.2 hw`.

Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hF.isClosed.isOpen_compl 0 h0`. Use `⟨min r 1, lt_min hr one_pos, fun w hw hlt => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖w‖` using `norm_pos_iff.mpr hne`. Establish `hlt1 : ‖w‖ < 1` using `lt_of_lt_of_le hlt (min_le_right _ _)`.

Establish `hltr : ‖w‖ < r` using `lt_of_lt_of_le hlt (min_le_left _ _)`. Establish `hwF : w ∈ F`. Use `⟨⟨w, hw, hne⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, norm_div, norm_one, norm_pow]`. Conclude with `one_le_one_div (pow_pos hpos _) (pow_le_one₀ hpos.le hlt1.le)`.

Conclude with `hball (by simpa using hltr) hwF`.
-/
theorem dg_sep (Λ : AddSubgroup ℂ) (h : Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0) :
    ∃ r > 0, ∀ w ∈ Λ, ‖w‖ < r → w = 0 := by
  have hsum : ∃ k : ℕ, 1 ≤ k ∧
      Summable (fun w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) := by
    by_contra hn
    push Not at hn
    apply h
    have h2 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 2 = 0 := tsum_eq_zero_of_not_summable (hn 2 (by norm_num))
    have h3 : Formalism.MainNotions.TaylorLogMetric.eisG Λ 3 = 0 := tsum_eq_zero_of_not_summable (hn 3 (by norm_num))
    simp [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, h2, h3]
  obtain ⟨k, hk, hs⟩ := hsum
  have hfin : Set.Finite {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖} := by
    have := hs.tendsto_cofinite_zero (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    refine (Filter.mem_cofinite.mp this).subset ?_
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right, not_lt]
    exact hw
  set F : Set ℂ := Subtype.val '' {w : {w : ℂ // w ∈ Λ ∧ w ≠ 0} | 1 ≤ ‖1 / (w : ℂ) ^ (2 * k)‖}
  have hF : F.Finite := hfin.image _
  have h0 : (0 : ℂ) ∈ Fᶜ := by
    rintro ⟨w, _, hw⟩
    exact w.2.2 hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl 0 h0
  refine ⟨min r 1, lt_min hr one_pos, fun w hw hlt => ?_⟩
  by_contra hne
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have hlt1 : ‖w‖ < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hltr : ‖w‖ < r := lt_of_lt_of_le hlt (min_le_left _ _)
  have hwF : w ∈ F := by
    refine ⟨⟨w, hw, hne⟩, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq, norm_div, norm_one, norm_pow]
    exact one_le_one_div (pow_pos hpos _) (pow_le_one₀ hpos.le hlt1.le)
  exact hball (by simpa using hltr) hwF

/- English proof (translation)
Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Establish `: ({0} : Set Λ) = Subtype.val ⁻¹' Metric.ball (0 : ℂ) r`. Use extensionality with `⟨w, hw⟩`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Establish `: w = 0` using `congrArg Subtype.val h0`. Simplify `hr` using `[this]`. Introduce `h`. Conclude with `Subtype.ext (H w hw h)`.

Rewrite using `[this]`. Conclude with `Metric.isOpen_ball.preimage continuous_subtype_val`.
-/
theorem dg_discrete (Λ : AddSubgroup ℂ) {r : ℝ} (hr : 0 < r) (H : ∀ w ∈ Λ, ‖w‖ < r → w = 0) :
    DiscreteTopology Λ := by
  apply discreteTopology_of_isOpen_singleton_zero
  have : ({0} : Set Λ) = Subtype.val ⁻¹' Metric.ball (0 : ℂ) r := by
    ext ⟨w, hw⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h0
      have : w = 0 := congrArg Subtype.val h0
      simpa [this] using hr
    · intro h
      exact Subtype.ext (H w hw h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/- English proof (translation)
Assume the negation of the conclusion as `htop`. Distinguish the cases in `hb : ∀ w ∈ Λ, w = 0`. Apply `h` to reduce the goal to its premises. Establish `: Λ = AddSubgroup.zmultiples 0`. Use extensionality with `w`.

Simplify using `only [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot]`. Conclude with `⟨hb w, fun hw => hw ▸ Λ.zero_mem⟩`. Rewrite using `[this]`. Conclude with `dg_discr_cyc 0`. Use `push Not at hb`.

Take `⟨w0, hw0, hw0ne⟩` from `hb`. Establish `hline : ∀ w ∈ Λ, ∃ t : ℝ, w = (t : ℂ) * w0`. Introduce `w hw`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`.

Apply `htop` to reduce the goal to its premises. Establish `hli : LinearIndependent ℝ ![w0, w]`. Rewrite using `[LinearIndependent.pair_iff' hw0ne]`. Introduce `a ha`. Conclude with `hno a (by rw [← ha, Complex.real_smul])`.

Use `hli.span_eq_top_of_card_eq_finrank' (by simp [Complex.finrank_real_complex])` as an intermediate fact. Rewrite using `[eq_top_iff, ← this]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Use `fin_cases i`.

Conclude with `hw0`. Conclude with `hw`. Set `φ : ℝ →+ ℂ` to `{ toFun := fun t => (t : ℂ) * w0 map_zero' := by simp map_add' := fun a b => by push_cast; ring }`. Use `set A : AddSubgroup ℝ := Λ.comap φ with hA`. Establish `hn0 : 0 < ‖w0‖` using `norm_pos_iff.mpr hw0ne`.

Establish `hdis : Disjoint (A : Set ℝ) (Set.Ioo 0 (r / ‖w0‖))`. Rewrite using `[Set.disjoint_left]`. Introduce `t ht hto`. Establish `hmem : (t : ℂ) * w0 ∈ Λ` using `ht`. Establish `hnorm : ‖(t : ℂ) * w0‖ < r`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hto.1]`. Use `hto.2` as an intermediate fact. Rewrite `this` using `[lt_div_iff₀ hn0]`. Then use the resulting hypothesis. Use `H _ hmem hnorm` as an intermediate fact. Break down `mul_eq_zero.mp this with h1 | h1` into its components or cases.

Conclude with `hto.1.ne' (by exact_mod_cast h1)`. Conclude with `hw0ne h1`. Take `⟨b, hbA⟩` from `AddSubgroup.cyclic_of_isolated_zero (div_pos hr hn0) hdis`. Apply `h` to reduce the goal to its premises. Establish `hbmem : (b : ℂ) * w0 ∈ Λ`.

Establish `: b ∈ A` using `by rw [hbA]; exact AddSubgroup.subset_closure rfl`. Conclude with `this`. Establish `: Λ = AddSubgroup.zmultiples ((b : ℂ) * w0)`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Take `⟨t, rfl⟩` from `hline w hw`. Establish `htA : t ∈ A` using `hw`. Rewrite `htA` using `[hbA, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff]`. Take `⟨n, rfl⟩` from `htA`.

Conclude with `AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]; ring⟩`. Introduce `hw`. Take `⟨n, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.mp hw`. Conclude with `Λ.zsmul_mem hbmem n`. Rewrite using `[this]`.

Conclude with `dg_discr_cyc _`.
-/
theorem dg_span (Λ : AddSubgroup ℂ) (h : Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0) {r : ℝ} (hr : 0 < r)
    (H : ∀ w ∈ Λ, ‖w‖ < r → w = 0) : Submodule.span ℝ (Λ : Set ℂ) = ⊤ := by
  by_contra htop
  by_cases hb : ∀ w ∈ Λ, w = 0
  · apply h
    have : Λ = AddSubgroup.zmultiples 0 := by
      ext w
      simp only [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot]
      exact ⟨hb w, fun hw => hw ▸ Λ.zero_mem⟩
    rw [this]; exact dg_discr_cyc 0
  push Not at hb
  obtain ⟨w0, hw0, hw0ne⟩ := hb
  have hline : ∀ w ∈ Λ, ∃ t : ℝ, w = (t : ℂ) * w0 := by
    intro w hw
    by_contra hno
    push Not at hno
    apply htop
    have hli : LinearIndependent ℝ ![w0, w] := by
      rw [LinearIndependent.pair_iff' hw0ne]
      intro a ha
      exact hno a (by rw [← ha, Complex.real_smul])
    have := hli.span_eq_top_of_card_eq_finrank' (by simp [Complex.finrank_real_complex])
    rw [eq_top_iff, ← this]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hw0
    · exact hw
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => (t : ℂ) * w0
      map_zero' := by simp
      map_add' := fun a b => by push_cast; ring }
  set A : AddSubgroup ℝ := Λ.comap φ with hA
  have hn0 : 0 < ‖w0‖ := norm_pos_iff.mpr hw0ne
  have hdis : Disjoint (A : Set ℝ) (Set.Ioo 0 (r / ‖w0‖)) := by
    rw [Set.disjoint_left]
    intro t ht hto
    have hmem : (t : ℂ) * w0 ∈ Λ := ht
    have hnorm : ‖(t : ℂ) * w0‖ < r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hto.1]
      have := hto.2
      rwa [lt_div_iff₀ hn0] at this
    have := H _ hmem hnorm
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hto.1.ne' (by exact_mod_cast h1)
    · exact hw0ne h1
  obtain ⟨b, hbA⟩ := AddSubgroup.cyclic_of_isolated_zero (div_pos hr hn0) hdis
  apply h
  have hbmem : (b : ℂ) * w0 ∈ Λ := by
    have : b ∈ A := by rw [hbA]; exact AddSubgroup.subset_closure rfl
    exact this
  have : Λ = AddSubgroup.zmultiples ((b : ℂ) * w0) := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, rfl⟩ := hline w hw
      have htA : t ∈ A := hw
      rw [hbA, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff] at htA
      obtain ⟨n, rfl⟩ := htA
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]; ring⟩
    · intro hw
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
      exact Λ.zsmul_mem hbmem n
  rw [this]; exact dg_discr_cyc _

/- English proof (translation)
Introduce `Λ h`. Take `⟨r, hr, H⟩` from `dg_sep Λ h`. Conclude with `⟨dg_discrete Λ hr H, dg_span Λ h hr H⟩`.
-/
theorem latOfDiscr_holds : LatOfDiscr := by
  intro Λ h
  obtain ⟨r, hr, H⟩ := dg_sep Λ h
  exact ⟨dg_discrete Λ hr H, dg_span Λ h hr H⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
