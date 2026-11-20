import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

/- English proof (translation)
Introduce `x hx` and use `((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt`.
-/
theorem pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U :=
  fun x hx => ((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/- English proof (translation)
Use `fun_prop`.
-/
theorem pa_aff_analytic {e : ℕ} (a : ℂ) (b : Fin e → ℂ) (y : Fin e → ℂ) :
    AnalyticAt ℂ (fun y : Fin e → ℂ => a • (y - b)) y :=
  by fun_prop

/- English proof (translation)
Introduce `k` and use `⟨A.holo k j, A.holo j k⟩`.
-/
theorem pa_compat_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (j : Fin A.n) : IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

/- English proof (translation)
Introduce `j`. Take `⟨h1, h2⟩` from `hψ j`. Use `⟨h1.mono ?_, h2.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`. Conclude with `⟨hx1, hx2.1⟩`.

Introduce and unpack `x ⟨hx1, hx2⟩`. Conclude with `⟨hx1.1, hx2⟩`.
-/
theorem pa_compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (s : Set X)
    (hs : IsOpen s) : IsCompatChart A (ψ.restrOpen s hs) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.1⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩

/- English proof (translation)
Introduce `j`. Take `⟨h1, h2⟩` from `hψ j`. Use `⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩` and prove the remaining obligations. Establish `hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z` using `by fun_prop`. Conclude with `AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv`.
-/
theorem pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv

/- English proof (translation)
Introduce `e X _ _ _ A`. Take `⟨χ, h0, h1, h2, h3⟩` from `ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover (fun i j => pa_holoSmooth _ _ (A.holo i j))`. Conclude with `⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩`.
-/
theorem existsPartition : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩

def AffineChartStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) (a : ℂ)
    (b : Fin e → ℂ), a ≠ 0 →
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧
      ψ.source = (A.chart j).source ∧ ∀ x ∈ ψ.source, ψ x = a • (A.chart j x - b)

/- English proof (translation)
Introduce `e X _ A j a b ha`. Conclude with `⟨(A.chart j).transHomeomorph (pa_aff a ha b), pa_compat_aff A _ (pa_compat_chart A j) a ha b, rfl, fun x _ => rfl⟩`.
-/
theorem affineChart : AffineChartStatement := by
  intro e X _ A j a b ha
  exact ⟨(A.chart j).transHomeomorph (pa_aff a ha b), pa_compat_aff A _ (pa_compat_chart A j) a ha b, rfl,
    fun x _ => rfl⟩

def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i

/- English proof (translation)
Introduce `e X _ A m ψ hψ hcov`. Use `⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩, fun j => ⟨j, rfl⟩⟩` and prove the remaining obligations. Introduce `j k z hz`. Take `⟨hz1, hz2⟩` from `hz`. Take `⟨l, hx⟩` from `A.cover ((ψ j).symm z)`.

Establish `hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source` using `((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)`. Establish `ha1` using `(hψ k l).1 (A.chart l ((ψ j).symm z)) ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩`. Establish `ha2` using `(hψ j l).2 z ⟨hz1, hx⟩`. Conclude with `(AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by`. Simplify using `only [Function.comp, (A.chart l).left_inv hw])`.
-/
theorem atlasOfCompat : AtlasOfCompatStatement := by
  intro e X _ A m ψ hψ hcov
  refine ⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩,
    fun j => ⟨j, rfl⟩⟩
  intro j k z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨l, hx⟩ := A.cover ((ψ j).symm z)
  have hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source :=
    ((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)
  have ha1 := (hψ k l).1 (A.chart l ((ψ j).symm z))
    ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩
  have ha2 := (hψ j l).2 z ⟨hz1, hx⟩
  exact (AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by
    simp only [Function.comp, (A.chart l).left_inv hw])

/- English proof (translation)
Introduce `e X _ _ _ A`. Establish `hloc : ∀ x : X, ∃ (j : Fin A.n) (r : ℝ), 0 < r ∧ x ∈ (A.chart j).source ∧ Metric.ball (A.chart j x) r ⊆ (A.chart j).target`. Introduce `x`. Take `⟨j, hj⟩` from `A.cover x`. Take `⟨r, hr, hb⟩` from `Metric.isOpen_iff.mp (A.chart j).open_target _ ((A.chart j).map_source hj)`.

Conclude with `⟨j, r, hr, hj, hb⟩`. Use `choose J R hR hJ hball using hloc`. Establish `ha : ∀ x, (((3 / R x : ℝ)) : ℂ) ≠ 0` using `fun x => Complex.ofReal_ne_zero.mpr (div_pos (by norm_num) (hR x)).ne'`. Set `ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)` to `fun x => (A.chart (J x)).transHomeomorph (pa_aff (((3 / R x : ℝ)) : ℂ) (ha x) (A.chart (J x) x))`. Establish `hψc : ∀ x, IsCompatChart A (ψ x)` using `fun x => pa_compat_aff A _ (pa_compat_chart A (J x)) _ (ha x) _`.

Set `U : X → Set X` to `fun x => (ψ x).source ∩ (ψ x) ⁻¹' Metric.ball 0 1`. Establish `hUo : ∀ x, IsOpen (U x)` using `fun x => (ψ x).isOpen_inter_preimage Metric.isOpen_ball`. Establish `hUx : ∀ x, x ∈ U x` using `fun x => by`. Use `⟨hJ x, ?_⟩` and prove the remaining obligations. Use `show (((3 / R x : ℝ)) : ℂ) • (A.chart (J x) x - A.chart (J x) x) ∈ Metric.ball (0 : Fin e → ℂ) 1`.

Simplify using the standard rewrite rules. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover U hUo (fun x _ => Set.mem_iUnion.mpr ⟨x, hUx x⟩)`. Set `φ : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ)` to `fun i => ψ (t.equivFin.symm i)`. Establish `hcov : ∀ x, ∃ i, x ∈ (φ i).source ∧ φ i x ∈ Metric.ball (0 : Fin e → ℂ) 1`. Introduce `x`.

Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.mp (ht (Set.mem_univ x))`. Use `⟨t.equivFin ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [φ, Equiv.symm_apply_apply]`. Conclude with `hxy`. Take `⟨B, hAB, hB1, hB2⟩` from `atlasOfCompat A φ (fun i => hψc _) (fun x => (hcov x).imp fun i h => h.1)`.

Use `⟨B, hAB, fun j => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hB2 j`. Rewrite using `[hi]`. Introduce `w hw`. Establish `hw' : ‖w‖ ≤ 2` using `by simpa using hw`.

Use `set y := t.equivFin.symm i`. Express the relevant statement in the definitionally equal form `(((3 / R y : ℝ)) : ℂ)⁻¹ • w + A.chart (J y) y ∈ (A.chart (J y)).target`. Apply `hball` to reduce the goal to its premises. Establish `hRy` using `hR y`. Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hRy), inv_div]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨i, hi1, hi2⟩` from `hcov x`. Take `⟨j, hj⟩` from `hB1 i`. Conclude with `⟨j, hj ▸ hi1, hj ▸ hi2⟩`.
-/
theorem regularAtlas : RegularAtlasStatement := by
  intro e X _ _ _ A
  have hloc : ∀ x : X, ∃ (j : Fin A.n) (r : ℝ), 0 < r ∧ x ∈ (A.chart j).source ∧
      Metric.ball (A.chart j x) r ⊆ (A.chart j).target := by
    intro x
    obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (A.chart j).open_target _ ((A.chart j).map_source hj)
    exact ⟨j, r, hr, hj, hb⟩
  choose J R hR hJ hball using hloc
  have ha : ∀ x, (((3 / R x : ℝ)) : ℂ) ≠ 0 := fun x =>
    Complex.ofReal_ne_zero.mpr (div_pos (by norm_num) (hR x)).ne'
  let ψ : X → OpenPartialHomeomorph X (Fin e → ℂ) := fun x =>
    (A.chart (J x)).transHomeomorph (pa_aff (((3 / R x : ℝ)) : ℂ) (ha x) (A.chart (J x) x))
  have hψc : ∀ x, IsCompatChart A (ψ x) := fun x =>
    pa_compat_aff A _ (pa_compat_chart A (J x)) _ (ha x) _
  let U : X → Set X := fun x => (ψ x).source ∩ (ψ x) ⁻¹' Metric.ball 0 1
  have hUo : ∀ x, IsOpen (U x) := fun x => (ψ x).isOpen_inter_preimage Metric.isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => by
    refine ⟨hJ x, ?_⟩
    show (((3 / R x : ℝ)) : ℂ) • (A.chart (J x) x - A.chart (J x) x) ∈ Metric.ball (0 : Fin e → ℂ) 1
    simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo (fun x _ => Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  let φ : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun i => ψ (t.equivFin.symm i)
  have hcov : ∀ x, ∃ i, x ∈ (φ i).source ∧ φ i x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simp only [φ, Equiv.symm_apply_apply]
    exact hxy
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A φ (fun i => hψc _) (fun x => (hcov x).imp fun i h => h.1)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := hB2 j
    rw [hi]
    intro w hw
    have hw' : ‖w‖ ≤ 2 := by simpa using hw
    set y := t.equivFin.symm i
    change (((3 / R y : ℝ)) : ℂ)⁻¹ • w + A.chart (J y) y ∈ (A.chart (J y)).target
    apply hball
    have hRy := hR y
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hRy), inv_div]
    calc R y / 3 * ‖w‖ ≤ R y / 3 * 2 := by gcongr
      _ < R y := by linarith
  · obtain ⟨i, hi1, hi2⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, hj ▸ hi1, hj ▸ hi2⟩

end

end ReciprocityTheory.AnForm.M
