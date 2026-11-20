import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepD

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

open Classical in

def bsExt (M : Set Y) (h : M → ℂ) (y : Y) : ℂ := if hy : y ∈ M then h ⟨y, hy⟩ else 0

def bsH (M : Set Y) (h : M → ℂ) (σ w0 : ι → Y → ℂ) (m : ℕ) (i : ι) (y : Y) : ℂ :=
  bsExt M h y * (σ i y * w0 i y ^ m)

def bsW (A : WeightedAtlas n Y ι La) (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (T' : ℕ) (y : Y) : ℝ :=
  A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))

/- English proof (translation)
Unfold `bsExt`. Rewrite using `[dif_pos hy]`.
-/
theorem bsE_ext_mem {M : Set Y} (h : M → ℂ) {y : Y} (hy : y ∈ M) : bsExt M h y = h ⟨y, hy⟩ := by
  unfold bsExt; rw [dif_pos hy]

/- English proof (translation)
Establish `hb` using `bsD_denom A hD hσ m`. Establish `hh' : Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y)`. Establish `: (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) = h`. Use function extensionality and compare the values at `fun y => bsE_ext_mem h y.2`. Rewrite using `[this]`.

Conclude with `hh`. Establish `hd` using `(holo_flat_iff A hD hF _).mp hh'`. Use `⟨fun i => ?_, fun i j y hy hi hj => ?_⟩` and prove the remaining obligations. Use `(hd i).mul (hb.1 i)` as an intermediate fact. Use `this.congr fun v _ => ?_` and prove the remaining obligations.

Simplify using `[bsH]`. Simplify using `only [bsH]`. Use `hb.2 i j y hy hi hj` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bsE_sec (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (h : A.Mset w0 s De → ℂ)
    (hh : Holo n (flatStein A hD hF).z h) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (bsH (A.Mset w0 s De) h σ w0 m) := by
  have hb := bsD_denom A hD hσ m
  have hh' : Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) := by
    have : (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) = h :=
      funext fun y => bsE_ext_mem h y.2
    rw [this]; exact hh
  have hd := (holo_flat_iff A hD hF _).mp hh'
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have := (hd i).mul (hb.1 i)
    refine this.congr fun v _ => ?_
    simp [bsH]
  · simp only [bsH]
    have := hb.2 i j y hy hi hj
    simp only at this
    rw [this]; ring

/- English proof (translation)
Take `⟨ha, hnσ, hZ, hSw, hd⟩` from `bsD_pos A hD hF hσ hX x x.2`. Establish `e1` using `bsC_nsq_prod A mu0 L (T' - 1) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) σ w0 (h x) x (by simp only [bsH]; rw [bsE_ext_mem h x.2])`. Establish `e2` using `bsC_sqn_ratio A L s w0 x x.2.1`. Establish `e3` using `bsC_sqn_ratio A L w w0 x x.2.1`. Establish `e4` using `exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw`.

Establish `hs0 : 0 ≤ A.sqn L s x` using `Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x`. Establish `hw0 : 0 ≤ A.sqn L w x` using `Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x`. Establish `hp : 0 ≤ A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x * bsW A L w s T' x` using `mul_nonneg (bsA_nsq_nonneg A _ _ x) (mul_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg hw0 _))`. Rewrite using `[← ENNReal.ofReal_mul hp]`. Use `congr 1`.

Establish `hc : ((T' - 1 : ℕ) : ℝ) - 1 / 2 = (T' : ℝ) - 3 / 2`. Rewrite using `[Nat.cast_sub hT]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `bsW`.

Rewrite using `[e1, e2, e3, e4, ← hc, ← mul_assoc]`. Conclude with `bsC_alg _ _ _ _ _ _ (T' - 1) ha hZ hSw`.
-/
theorem bsE_heq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (h : A.Mset w0 s De → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖h x‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by
  obtain ⟨ha, hnσ, hZ, hSw, hd⟩ := bsD_pos A hD hF hσ hX x x.2
  have e1 := bsC_nsq_prod A mu0 L (T' - 1) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) σ w0 (h x) x
    (by simp only [bsH]; rw [bsE_ext_mem h x.2])
  have e2 := bsC_sqn_ratio A L s w0 x x.2.1
  have e3 := bsC_sqn_ratio A L w w0 x x.2.1
  have e4 := exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw
  have hs0 : 0 ≤ A.sqn L s x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x
  have hw0 : 0 ≤ A.sqn L w x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x
  have hp : 0 ≤ A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x :=
    mul_nonneg (bsA_nsq_nonneg A _ _ x)
      (mul_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg hw0 _))
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  have hc : ((T' - 1 : ℕ) : ℝ) - 1 / 2 = (T' : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hT]; push_cast; ring
  unfold bsW
  rw [e1, e2, e3, e4, ← hc, ← mul_assoc]
  exact bsC_alg _ _ _ _ _ _ (T' - 1) ha hZ hSw

/- English proof (translation)
Take `⟨ha, -, hZ, -, -⟩` from `bsD_pos A hD hF hσ hX x hx`. Rewrite using `[bsC_sqn_ratio A L s w0 x hx.1]`. Check the signs of the components of the expression.
-/
theorem bsE_sqn_s_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    {x : Y} (hx : x ∈ A.Mset w0 s De) : 0 < A.sqn L s x := by
  obtain ⟨ha, -, hZ, -, -⟩ := bsD_pos A hD hF hσ hX x hx
  rw [bsC_sqn_ratio A L s w0 x hx.1]; positivity

open Classical in
/- English proof (translation)
Establish `hMo` using `isOpen_Mset A (De := De) hD`. Establish `h1` using `bsC_nsq_contOn A (bsE_sec A hD hF hσ h hh (T' - 1)) hMo`. Establish `h2 : ContinuousOn (bsW A L w s T') (A.Mset w0 s De)`. Unfold `bsW`. Use `ContinuousOn.mul ?_ ?_` and prove the remaining obligations.

Conclude with `(bsA_sqn_cont A hD.sec_s).continuousOn.rpow_const fun x hx => Or.inl (bsE_sqn_s_pos A hD hF hσ hX hx).ne'`. Conclude with `(bsA_sqn_cont A hD.sec_w).continuousOn.rpow_const fun x _ => Or.inl (bsA_sqn_pos A (hD.no_common_zero x)).ne'`. Conclude with `ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn (h1.mul h2)) continuousOn_const hMo.measurableSet`.
-/
theorem bsE_meas (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h) :
    Measurable ((A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y * bsW A L w s T' y))
      (fun _ => 0)) := by
  have hMo := isOpen_Mset A (De := De) hD
  have h1 := bsC_nsq_contOn A (bsE_sec A hD hF hσ h hh (T' - 1)) hMo
  have h2 : ContinuousOn (bsW A L w s T') (A.Mset w0 s De) := by
    unfold bsW
    refine ContinuousOn.mul ?_ ?_
    · exact (bsA_sqn_cont A hD.sec_s).continuousOn.rpow_const fun x hx =>
        Or.inl (bsE_sqn_s_pos A hD hF hσ hX hx).ne'
    · exact (bsA_sqn_cont A hD.sec_w).continuousOn.rpow_const fun x _ =>
        Or.inl (bsA_sqn_pos A (hD.no_common_zero x)).ne'
  exact ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn (h1.mul h2)) continuousOn_const hMo.measurableSet

open Classical in
/- English proof (translation)
Rewrite using `[lintegral_flat A hD hF _ (bsE_meas A hD hF hσ hX T' (hh k) (hhol k))]`. Use `lt_of_le_of_lt (lintegral_mono fun x => ?_) hbd` and prove the remaining obligations. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ x.2, bsE_heq A hD hF hσ hX T' hT (hh k) x]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h1 : ‖hh k x‖ ^ 2 ≤ ∑ j, ‖hh j x‖ ^ 2` using `Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ k)`.

Establish `h2 : 0 ≤ (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2))` using `Real.rpow_nonneg (by positivity) _`. Establish `h3` using `Real.exp_pos (-bsPh0 A w w0 s mu0 σ x)`. Use `gcongr`.
-/
theorem bsE_int (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (hh : Fin n → A.Mset w0 s De → ℂ)
    (hhol : ∀ k, Holo n (flatStein A hD hF).z (hh k)) (k : Fin n)
    (hbd : ∫⁻ x, ENNReal.ofReal ((∑ j, ‖hh j x‖ ^ 2) *
          (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤) :
    ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) (hh k) σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤ := by
  rw [lintegral_flat A hD hF _ (bsE_meas A hD hF hσ hX T' (hh k) (hhol k))]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hbd
  rw [Set.piecewise_eq_of_mem _ _ _ x.2, bsE_heq A hD hF hσ hX T' hT (hh k) x]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖hh k x‖ ^ 2 ≤ ∑ j, ‖hh j x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ k)
  have h2 : 0 ≤ (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^
      (-((T' : ℝ) - 3 / 2)) := Real.rpow_nonneg (by positivity) _
  have h3 := Real.exp_pos (-bsPh0 A w w0 s mu0 σ x)
  gcongr

open Classical in
/- English proof (translation)
Take `⟨C, hC⟩` from `hD.s_le_w`. Establish `hMo` using `isOpen_Mset A (De := De) hD`. Use `set C' := max C 1 with hC'`. Use `set K := A.sqn L w y + 1 with hK`. Establish `hK0 : 0 < K`.

Use `Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => bsA_nsq_nonneg A L (w k) y` as an intermediate fact. Simplify using `only [sqn] at hK ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC'1 : 1 ≤ C'` using `le_max_right _ _`. Establish `hp : 0 ≤ (T' : ℝ) - 3 / 2`.

Establish `: (2 : ℝ) ≤ T'` using `by exact_mod_cast hT`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set c := (C' * K) ^ (-((T' : ℝ) - 3 / 2)) * K ^ (-(1 / 2 : ℝ)) with hc`. Establish `hc0 : 0 < c` using `mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hK0 _)`. Use `set U := {y' | A.sqn L w y' < K} with hU`.

Establish `hUo : IsOpen U` using `isOpen_lt (bsA_sqn_cont A hD.sec_w) continuous_const`. Establish `hyU : y ∈ U` using `by simp [hU, hK]`. Use `⟨U, hUo.mem_nhds hyU, ?_⟩` and prove the remaining obligations. Use `set ψ := (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y * bsW A L w s T' y)) (fun _ => 0) with hψ`. Establish `hbound : ∀ x ∈ U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ≤ ENNReal.ofReal c⁻¹ * ψ x`.

Introduce `x hx`. Rewrite using `[hψ, Set.piecewise_eq_of_mem _ _ _ hx.2, ← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hs` using `bsE_sqn_s_pos A hD hF hσ hX hx.2`. Establish `hw` using `bsA_sqn_pos A (la := L) (hD.no_common_zero x) (w := w)`.

Establish `hwK : A.sqn L w x ≤ K` using `le_of_lt hx.1`. Establish `hsK : A.sqn L s x ≤ C' * K`. Combine the equalities or inequalities in the displayed calculation. Establish `hW : c ≤ bsW A L w s T' x`. Unfold `bsW`.

Conclude with `mul_le_mul (Real.rpow_le_rpow_of_nonpos hs hsK (by linarith)) (Real.rpow_le_rpow_of_nonpos hw hwK (by norm_num)) (Real.rpow_pos_of_pos hK0 _).le (Real.rpow_nonneg hs.le _)`. Establish `hn0` using `bsA_nsq_nonneg A (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x * bsW A L w s T' x) := by gcongr`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bsE_loc (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 2 ≤ T') (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h)
    (hint : ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤) (y : Y) :
    ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu < ⊤ := by
  obtain ⟨C, hC⟩ := hD.s_le_w
  have hMo := isOpen_Mset A (De := De) hD
  set C' := max C 1 with hC'
  set K := A.sqn L w y + 1 with hK
  have hK0 : 0 < K := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => bsA_nsq_nonneg A L (w k) y
    simp only [sqn] at hK ⊢; linarith
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hp : 0 ≤ (T' : ℝ) - 3 / 2 := by
    have : (2 : ℝ) ≤ T' := by exact_mod_cast hT
    linarith
  set c := (C' * K) ^ (-((T' : ℝ) - 3 / 2)) * K ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hK0 _)
  set U := {y' | A.sqn L w y' < K} with hU
  have hUo : IsOpen U := isOpen_lt (bsA_sqn_cont A hD.sec_w) continuous_const
  have hyU : y ∈ U := by simp [hU, hK]
  refine ⟨U, hUo.mem_nhds hyU, ?_⟩
  set ψ := (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) with hψ
  have hbound : ∀ x ∈ U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ≤
      ENNReal.ofReal c⁻¹ * ψ x := by
    intro x hx
    rw [hψ, Set.piecewise_eq_of_mem _ _ _ hx.2, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs := bsE_sqn_s_pos A hD hF hσ hX hx.2
    have hw := bsA_sqn_pos A (la := L) (hD.no_common_zero x) (w := w)
    have hwK : A.sqn L w x ≤ K := le_of_lt hx.1
    have hsK : A.sqn L s x ≤ C' * K := by
      calc A.sqn L s x ≤ C * A.sqn L w x := hC x
        _ ≤ C' * A.sqn L w x := mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le
        _ ≤ C' * K := mul_le_mul_of_nonneg_left hwK (by positivity)
    have hW : c ≤ bsW A L w s T' x := by
      unfold bsW
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hs hsK (by linarith))
        (Real.rpow_le_rpow_of_nonpos hw hwK (by norm_num)) (Real.rpow_pos_of_pos hK0 _).le
        (Real.rpow_nonneg hs.le _)
    have hn0 := bsA_nsq_nonneg A (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
    calc A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
        = c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x * c) := by
          field_simp
      _ ≤ c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
          bsW A L w s T' x) := by gcongr
  calc ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
        (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu
      ≤ ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        setLIntegral_mono' (hUo.inter hMo).measurableSet hbound
    _ ≤ ∫⁻ x in A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        lintegral_mono_set Set.inter_subset_right
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x in A.Mset w0 s De, ψ x ∂A.mu :=
        lintegral_const_mul _ (bsE_meas A hD hF hσ hX T' h hh)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

end

end ReciprocityTheory.L2DbarEstimates.Y
