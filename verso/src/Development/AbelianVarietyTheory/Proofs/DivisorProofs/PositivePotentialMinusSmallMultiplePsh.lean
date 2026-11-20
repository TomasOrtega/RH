import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

namespace GlobalTheory.PosDom

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Use `norm_cast`.
-/
theorem two_le_top : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

/- English proof (translation)
Use `set c := A.chart j with hc`. Use `set q := c.symm z with hq`. Take `⟨W, hWo, hqW, G, hG, hGeq⟩` from `hQ.2 x p q ⟨hx, hp⟩`. Establish `hGa : AnalyticAt ℂ (G ∘ c.symm) z` using `hG j z ⟨hz, hqW⟩`. Establish `hRe : ContDiffAt ℝ 2 (fun w => ((G ∘ c.symm) w).re) z`.

Use `(Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `hQp : ContDiffAt ℝ 2 (Q.φ p ∘ c.symm) z` using `((hQ.1 p j).of_le two_le_top).contDiffAt ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (Q.isOpen_U p)).mem_nhds ⟨hz, hp⟩)`. Establish `hbase : Q.φ x ∘ c.symm =ᶠ[𝓝 z] fun w => (Q.φ p ∘ c.symm) w + 1 * ((G ∘ c.symm) w).re`. Establish `hopen : IsOpen (W ∩ Q.U x ∩ Q.U p)` using `(hWo.inter (Q.isOpen_U x)).inter (Q.isOpen_U p)`.

Establish `: ∀ᶠ w in 𝓝 z, c.symm w ∈ W ∩ Q.U x ∩ Q.U p` using `(c.continuousAt_symm hz).preimage_mem_nhds (hopen.mem_nhds ⟨⟨hqW, hx⟩, hp⟩)`. Use `filter_upwards [this] with w hw`. Use `hGeq (c.symm w) hw` as an intermediate fact. Simplify using `only [Function.comp_apply, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[levi_congr hbase, levi_add_smul 1 hQp hRe, levi_re_analytic hGa]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_base_change (A : FinHolAtlas e X) (Q : LocPot X) (hQ : IsPotential A Q) (x p : X)
    (j : Fin A.n) (z : Fin e → ℂ) (hz : z ∈ (A.chart j).target)
    (hx : (A.chart j).symm z ∈ Q.U x) (hp : (A.chart j).symm z ∈ Q.U p) (u : Fin e → ℂ) :
    levi (Q.φ x ∘ (A.chart j).symm) z u = levi (Q.φ p ∘ (A.chart j).symm) z u := by
  set c := A.chart j with hc
  set q := c.symm z with hq
  obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hQ.2 x p q ⟨hx, hp⟩
  have hGa : AnalyticAt ℂ (G ∘ c.symm) z := hG j z ⟨hz, hqW⟩
  have hRe : ContDiffAt ℝ 2 (fun w => ((G ∘ c.symm) w).re) z := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have hQp : ContDiffAt ℝ 2 (Q.φ p ∘ c.symm) z :=
    ((hQ.1 p j).of_le two_le_top).contDiffAt
      ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (Q.isOpen_U p)).mem_nhds ⟨hz, hp⟩)
  have hbase : Q.φ x ∘ c.symm =ᶠ[𝓝 z]
      fun w => (Q.φ p ∘ c.symm) w + 1 * ((G ∘ c.symm) w).re := by
    have hopen : IsOpen (W ∩ Q.U x ∩ Q.U p) := (hWo.inter (Q.isOpen_U x)).inter (Q.isOpen_U p)
    have : ∀ᶠ w in 𝓝 z, c.symm w ∈ W ∩ Q.U x ∩ Q.U p :=
      (c.continuousAt_symm hz).preimage_mem_nhds (hopen.mem_nhds ⟨⟨hqW, hx⟩, hp⟩)
    filter_upwards [this] with w hw
    have := hGeq (c.symm w) hw
    simp only [Function.comp_apply, one_mul]
    linarith
  rw [levi_congr hbase, levi_add_smul 1 hQp hRe, levi_re_analytic hGa]
  ring

/- English proof (translation)
Use `set c := A.chart j with hc`. Use `set O := c.target ∩ c.symm ⁻¹' (P.U p ∩ Ω.U p) with hO`. Establish `hOo : IsOpen O` using `c.continuousOn_symm.isOpen_inter_preimage c.open_target ((P.isOpen_U p).inter (Ω.isOpen_U p))`. Establish `hpO : c p ∈ O` using `⟨c.map_source hp, by`. Simplify using `only [Set.mem_preimage, c.left_inv hp]`.

Conclude with `⟨P.mem_U p, Ω.mem_U p⟩⟩`. Take `⟨r, hr, hrO⟩` from `Metric.isOpen_iff.1 hOo _ hpO`. Establish `hcb : Metric.closedBall (c p) (r / 2) ⊆ O` using `(Metric.closedBall_subset_ball (by linarith)).trans hrO`. Establish `hPs : ContDiffOn ℝ 2 (P.φ p ∘ c.symm) O` using `((hP.1 p j).of_le two_le_top).mono (fun y hy => ⟨hy.1, hy.2.1⟩)`. Establish `hΩs : ContDiffOn ℝ 2 (Ω.φ p ∘ c.symm) O` using `((hΩ.1 p j).of_le two_le_top).mono (fun y hy => ⟨hy.1, hy.2.2⟩)`.

Use `set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 with hK`. Establish `hKc : IsCompact K` using `(isCompact_closedBall _ _).prod (isCompact_sphere _ _)`. Establish `hKO : K ⊆ O ×ˢ Set.univ` using `Set.prod_mono hcb (Set.subset_univ _)`. Establish `hpos' : ∀ q ∈ K, 0 < levi (P.φ p ∘ c.symm) q.1 q.2`. Introduce and unpack `⟨y, u⟩ ⟨hy, hu⟩`.

Use `hpos p j y ⟨(hcb hy).1, (hcb hy).2.1⟩ u ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hu`. Establish `hcont : ContinuousOn (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi (Ω.φ p ∘ c.symm) q.1 q.2 / levi (P.φ p ∘ c.symm) q.1 q.2) K` using `((continuousOn_levi hOo hΩs).mono hKO).div ((continuousOn_levi hOo hPs).mono hKO) (fun q hq => (hpos' q hq).ne')`. Take `⟨m, hm⟩` from `hKc.bddAbove_image hcont`.

Use `⟨r / 2, by linarith, m, hcb, fun y hy u => ?_⟩` and prove the remaining obligations. Break down `eq_or_ne u 0 with rfl | hu` into its components or cases. Simplify using `[levi_zero]`. Establish `hn : 0 < ‖u‖` using `norm_pos_iff.2 hu`. Take `⟨v, hv'⟩ : ∃ v : Fin e → ℂ, v = ‖u‖⁻¹ • u` from `⟨_, rfl⟩`.

Establish `hv : v ∈ Metric.sphere (0 : Fin e → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Establish `hq : (y, v) ∈ K` using `⟨hy, hv⟩`. Establish `h1 : levi (Ω.φ p ∘ c.symm) y v / levi (P.φ p ∘ c.symm) y v ≤ m` using `hm ⟨(y, v), hq, rfl⟩`. Establish `h2` using `hpos' _ hq`.

Establish `h3 : levi (Ω.φ p ∘ c.symm) y v ≤ m * levi (P.φ p ∘ c.symm) y v`. Rewrite `h1` using `[div_le_iff₀ h2]`. Then use the resulting hypothesis. Take `⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖` from `⟨_, rfl⟩`. Establish `huv : u = s • v`. Rewrite using `[hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`.

Rewrite using `[huv, levi_smul_dir, levi_smul_dir]`. Establish `: 0 ≤ s ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem local_ratio (A : FinHolAtlas e X) (P Ω : LocPot X) (hP : IsPotential A P)
    (hpos : IsPosPot A P) (hΩ : IsPotential A Ω) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U p ∩ Ω.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ m * levi (P.φ p ∘ (A.chart j).symm) y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (P.U p ∩ Ω.U p) with hO
  have hOo : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    ((P.isOpen_U p).inter (Ω.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨P.mem_U p, Ω.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have hPs : ContDiffOn ℝ 2 (P.φ p ∘ c.symm) O :=
    ((hP.1 p j).of_le two_le_top).mono (fun y hy => ⟨hy.1, hy.2.1⟩)
  have hΩs : ContDiffOn ℝ 2 (Ω.φ p ∘ c.symm) O :=
    ((hΩ.1 p j).of_le two_le_top).mono (fun y hy => ⟨hy.1, hy.2.2⟩)
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (P.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.1⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin e → ℂ) × (Fin e → ℂ) =>
      levi (Ω.φ p ∘ c.symm) q.1 q.2 / levi (P.φ p ∘ c.symm) q.1 q.2) K :=
    ((continuousOn_levi hOo hΩs).mono hKO).div ((continuousOn_levi hOo hPs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨m, hm⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, m, hcb, fun y hy u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin e → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : levi (Ω.φ p ∘ c.symm) y v / levi (P.φ p ∘ c.symm) y v ≤ m :=
      hm ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : levi (Ω.φ p ∘ c.symm) y v ≤ m * levi (P.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir]
    have : 0 ≤ s ^ 2 := by positivity
    nlinarith

/- English proof (translation)
Establish `hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source` using `fun p => Classical.choose_spec (A.cover p)`. Establish `key` using `fun p => local_ratio A P Ω hP hpos hΩ p (chartIdx A p) (hsrc p)`. Use `choose r hr m hsub hbd using key`. Set `V : X → Set X` to `fun p => (A.chart (chartIdx A p)).source ∩ (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)`. Establish `hVo : ∀ p, IsOpen (V p)` using `fun p => (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball`.

Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover V hVo (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)`. Use `set C := ∑ p ∈ t, |m p| with hC`. Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg (fun i _ => abs_nonneg (m i))`. Use `⟨1 / (1 + C), by positivity, ?_⟩` and prove the remaining obligations. Use `set κ := 1 / (1 + C) with hκ`.

Establish `hκ0 : 0 < κ` using `by positivity`. Introduce `x i y hy v`. Take `⟨hyi, hyU⟩` from `hy`. Establish `hqxP : (A.chart i).symm y ∈ P.U x` using `hyU.1`. Establish `hqxΩ : (A.chart i).symm y ∈ Ω.U x` using `hyU.2`.

Use `set q := (A.chart i).symm y with hq`. Choose the witnesses or unpack the hypotheses as in `⟨p, hpt, hqV⟩ : ∃ p ∈ t, q ∈ V p := by`. Simplify using `using ht (Set.mem_univ q)`. Use `set j := chartIdx A p with hj`. Use `set c := A.chart j with hc`.

Establish `hqs : q ∈ c.source` using `hqV.1`. Establish `hqb : c q ∈ Metric.ball (c p) (r p)` using `hqV.2`. Establish `hcqO` using `hsub p (Metric.ball_subset_closedBall hqb)`. Establish `hcqt : c q ∈ c.target` using `c.map_source hqs`. Establish `hsc : c.symm (c q) = q` using `c.left_inv hqs`.

Establish `hqp : q ∈ P.U p ∩ Ω.U p`. Use `hcqO.2` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, hsc]`. Then use the resulting hypothesis. Use `set τ := c ∘ (A.chart i).symm with hτd`. Establish `hτ : AnalyticAt ℂ τ y` using `A.holo i j y ⟨hyi, hqs⟩`.

Establish `hτy : τ y = c q` using `rfl`. Set `F : X → ℝ` to `fun z => P.φ x z + -κ * Ω.φ x z`. Express the relevant statement in the definitionally equal form `0 ≤ levi (F ∘ (A.chart i).symm) y v`. Establish `hgerm : F ∘ (A.chart i).symm =ᶠ[𝓝 y] (F ∘ c.symm) ∘ τ`. Establish `: ∀ᶠ y' in 𝓝 y, (A.chart i).symm y' ∈ c.source` using `((A.chart i).continuousAt_symm hyi).preimage_mem_nhds (c.open_source.mem_nhds hqs)`.

Use `filter_upwards [this] with y' hy'`. Simplify using `only [Function.comp_apply, τ, c.left_inv hy']`. Establish `hPx : ContDiffAt ℝ 2 (P.φ x ∘ c.symm) (c q)` using `((hP.1 x j).of_le two_le_top).contDiffAt ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (P.isOpen_U x)).mem_nhds ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hqxP⟩)`. Establish `hΩx : ContDiffAt ℝ 2 (Ω.φ x ∘ c.symm) (c q)` using `((hΩ.1 x j).of_le two_le_top).contDiffAt ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (Ω.isOpen_U x)).mem_nhds ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hqxΩ⟩)`. Establish `hFA : ContDiffAt ℝ 2 (F ∘ c.symm) (c q)` using `hPx.add (contDiffAt_const.mul hΩx)`.

Rewrite using `[levi_congr hgerm, levi_comp v hτ (by rw [hτy]; exact hFA), hτy]`. Use `set u := fderiv ℂ τ y v`. Establish `hsplit : levi (F ∘ c.symm) (c q) u = levi (P.φ x ∘ c.symm) (c q) u + -κ * levi (Ω.φ x ∘ c.symm) (c q) u` using `levi_add_smul (-κ) hPx hΩx u`. Establish `hPeq` using `levi_base_change A P hP x p j (c q) hcqt (by rw [hsc]; exact hqxP) (by rw [hsc]; exact hqp.1) u`. Establish `hΩeq` using `levi_base_change A Ω hΩ x p j (c q) hcqt (by rw [hsc]; exact hqxΩ) (by rw [hsc]; exact hqp.2) u`.

Establish `hLP : 0 ≤ levi (P.φ p ∘ c.symm) (c q) u`. Break down `eq_or_ne u 0 with h0 | h0` into its components or cases. Rewrite using `[h0, levi_zero]`. Conclude with `(hpos p j (c q) ⟨hcqt, hcqO.2.1⟩ u h0).le`. Establish `hb` using `hbd p (c q) (Metric.ball_subset_closedBall hqb) u`.

Establish `hmC : |m p| ≤ C` using `Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt`. Establish `hκm : κ * |m p| ≤ 1`. Rewrite using `[hκ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : levi (Ω.φ p ∘ c.symm) (c q) u ≤ |m p| * levi (P.φ p ∘ c.symm) (c q) u` using `hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hLP)`.

Establish `h2 : κ * levi (Ω.φ p ∘ c.symm) (c q) u ≤ levi (P.φ p ∘ c.symm) (c q) u`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsplit, hPeq, hΩeq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_pos_sub_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (P Ω : LocPot X) (hP : IsPotential A P) (hpos : IsPosPot A P)
    (hΩ : IsPotential A Ω) : ∃ k : ℝ, 0 < k ∧ IsPsh A (P + Ω.rsmul (-k)) := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source :=
    fun p => Classical.choose_spec (A.cover p)
  have key := fun p => local_ratio A P Ω hP hpos hΩ p (chartIdx A p) (hsrc p)
  choose r hr m hsub hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)
  set C := ∑ p ∈ t, |m p| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
  refine ⟨1 / (1 + C), by positivity, ?_⟩
  set κ := 1 / (1 + C) with hκ
  have hκ0 : 0 < κ := by positivity
  intro x i y hy v
  obtain ⟨hyi, hyU⟩ := hy
  have hqxP : (A.chart i).symm y ∈ P.U x := hyU.1
  have hqxΩ : (A.chart i).symm y ∈ Ω.U x := hyU.2
  set q := (A.chart i).symm y with hq
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, q ∈ V p := by
    simpa using ht (Set.mem_univ q)
  set j := chartIdx A p with hj
  set c := A.chart j with hc
  have hqs : q ∈ c.source := hqV.1
  have hqb : c q ∈ Metric.ball (c p) (r p) := hqV.2
  have hcqO := hsub p (Metric.ball_subset_closedBall hqb)
  have hcqt : c q ∈ c.target := c.map_source hqs
  have hsc : c.symm (c q) = q := c.left_inv hqs
  have hqp : q ∈ P.U p ∩ Ω.U p := by
    have := hcqO.2; rwa [Set.mem_preimage, hsc] at this
  set τ := c ∘ (A.chart i).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo i j y ⟨hyi, hqs⟩
  have hτy : τ y = c q := rfl
  let F : X → ℝ := fun z => P.φ x z + -κ * Ω.φ x z
  change 0 ≤ levi (F ∘ (A.chart i).symm) y v
  have hgerm : F ∘ (A.chart i).symm =ᶠ[𝓝 y] (F ∘ c.symm) ∘ τ := by
    have : ∀ᶠ y' in 𝓝 y, (A.chart i).symm y' ∈ c.source :=
      ((A.chart i).continuousAt_symm hyi).preimage_mem_nhds (c.open_source.mem_nhds hqs)
    filter_upwards [this] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hPx : ContDiffAt ℝ 2 (P.φ x ∘ c.symm) (c q) :=
    ((hP.1 x j).of_le two_le_top).contDiffAt
      ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (P.isOpen_U x)).mem_nhds
        ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hqxP⟩)
  have hΩx : ContDiffAt ℝ 2 (Ω.φ x ∘ c.symm) (c q) :=
    ((hΩ.1 x j).of_le two_le_top).contDiffAt
      ((c.continuousOn_symm.isOpen_inter_preimage c.open_target (Ω.isOpen_U x)).mem_nhds
        ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hqxΩ⟩)
  have hFA : ContDiffAt ℝ 2 (F ∘ c.symm) (c q) := hPx.add (contDiffAt_const.mul hΩx)
  rw [levi_congr hgerm, levi_comp v hτ (by rw [hτy]; exact hFA), hτy]
  set u := fderiv ℂ τ y v
  have hsplit : levi (F ∘ c.symm) (c q) u =
      levi (P.φ x ∘ c.symm) (c q) u + -κ * levi (Ω.φ x ∘ c.symm) (c q) u :=
    levi_add_smul (-κ) hPx hΩx u
  have hPeq := levi_base_change A P hP x p j (c q) hcqt
    (by rw [hsc]; exact hqxP) (by rw [hsc]; exact hqp.1) u
  have hΩeq := levi_base_change A Ω hΩ x p j (c q) hcqt
    (by rw [hsc]; exact hqxΩ) (by rw [hsc]; exact hqp.2) u
  have hLP : 0 ≤ levi (P.φ p ∘ c.symm) (c q) u := by
    rcases eq_or_ne u 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (hpos p j (c q) ⟨hcqt, hcqO.2.1⟩ u h0).le
  have hb := hbd p (c q) (Metric.ball_subset_closedBall hqb) u
  have hmC : |m p| ≤ C := Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt
  have hκm : κ * |m p| ≤ 1 := by
    rw [hκ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have h1 : levi (Ω.φ p ∘ c.symm) (c q) u ≤ |m p| * levi (P.φ p ∘ c.symm) (c q) u :=
    hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hLP)
  have h2 : κ * levi (Ω.φ p ∘ c.symm) (c q) u ≤ levi (P.φ p ∘ c.symm) (c q) u := by
    calc κ * levi (Ω.φ p ∘ c.symm) (c q) u
        ≤ κ * (|m p| * levi (P.φ p ∘ c.symm) (c q) u) := mul_le_mul_of_nonneg_left h1 hκ0.le
      _ = (κ * |m p|) * levi (P.φ p ∘ c.symm) (c q) u := by ring
      _ ≤ 1 * levi (P.φ p ∘ c.symm) (c q) u := mul_le_mul_of_nonneg_right hκm hLP
      _ = _ := one_mul _
  rw [hsplit, hPeq, hΩeq]
  linarith

end

end GlobalTheory.PosDom
