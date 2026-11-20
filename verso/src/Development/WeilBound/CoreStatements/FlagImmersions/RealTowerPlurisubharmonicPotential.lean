import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.WeilBound.CoreStatements.FlagImmersions.DifferentiableAtAffCoord

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)

namespace RootFieldNumerics.Levi

/- English proof (translation)
Proceed by induction on `n, h using Nat.le_induction with`. Consider the case `base`. Rewrite using `[sub_self]`. Use `Finset.sum_eq_zero fun i hi => if_neg ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Consider the case `succ n hn ih => rw [Finset.sum_range_succ, ih, if_pos hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem telescope (g : ℕ → ℝ) (k n : ℕ) (h : k ≤ n) :
    ∑ i ∈ Finset.range n, (if k ≤ i then g i - g (i + 1) else 0) = g k - g n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => if_neg ?_
    have := Finset.mem_range.1 hi
    omega
  | succ n hn ih => rw [Finset.sum_range_succ, ih, if_pos hn]; ring

/- English proof (translation)
Use `set g : ℕ → ℝ := fun i => if h : i < N then lam (ψ, ⟨i, h⟩) else 0 with hgdef`. Establish `hg : ∀ k : Fin N, PB.gap lam (ψ, k) = g k - g (k + 1)`. Introduce `k`. Simplify using `only [PB.gap, PB.gapX, map_sub, eval_X, hgdef, dif_pos k.2]`. Use `split_ifs with h`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`.

Simplify using `only [Fin.le_iff_val_le_val, hg]`. Use `_ = ∑ i ∈ Finset.range N, (if (j : ℕ) ≤ i then g i - g (i + 1) else 0) := Fin.sum_univ_eq_sum_range (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) N`. Use `_ = g j - g N := telescope g j N j.2.le`. Use `_ = lam (ψ, j) := by simp [hgdef]`.
-/
private theorem sum_gap_of_le_eq {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (ψ : Ψ) (j : Fin N) :
    ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0) = lam (ψ, j) := by
  set g : ℕ → ℝ := fun i => if h : i < N then lam (ψ, ⟨i, h⟩) else 0 with hgdef
  have hg : ∀ k : Fin N, PB.gap lam (ψ, k) = g k - g (k + 1) := by
    intro k
    simp only [PB.gap, PB.gapX, map_sub, eval_X, hgdef, dif_pos k.2]
    split_ifs with h
    · simp
    · simp
  calc ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0)
      = ∑ k : Fin N, (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) k := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.le_iff_val_le_val, hg]
    _ = ∑ i ∈ Finset.range N, (if (j : ℕ) ≤ i then g i - g (i + 1) else 0) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) N
    _ = g j - g N := telescope g j N j.2.le
    _ = lam (ψ, j) := by simp [hgdef]

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Fintype.sum_prod_type]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `ψ _`. Establish `hI : ∀ k : Fin N, ∑ j ∈ Finset.Iic k, f (ψ, j) = ∑ j : Fin N, if j ≤ k then f (ψ, j) else 0`. Introduce `k`.

Rewrite using `[← Finset.sum_filter]`. Apply `Finset.sum_congr` to reduce the goal to its premises. Use extensionality with `j`. Simplify using the standard rewrite rules. Introduce `j _`.

Both sides reduce to the same expression. Simplify using `only [hI, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[← sum_gap_of_le_eq lam ψ j, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sum_gap_mul {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam f : Ψ × Fin N → ℝ) :
    ∑ p, PB.gap lam p * ∑ k ∈ Finset.Iic p.2, f (p.1, k) = ∑ p, lam p * f p := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ψ _
  have hI : ∀ k : Fin N, ∑ j ∈ Finset.Iic k, f (ψ, j) = ∑ j : Fin N, if j ≤ k then f (ψ, j) else 0 := by
    intro k
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp
    · intro j _
      rfl
  simp only [hI, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_gap_of_le_eq lam ψ j, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hsm : L.h (torusSmul c z) = (∏ k, ‖c k‖ ^ L.a k) * L.h z` using `L.smul c z hc`. Establish `hpos : 0 < L.h z` using `L.pos z hz`. Establish `hprod : ∀ k ∈ (Finset.univ : Finset K), ‖c k‖ ^ L.a k ≠ 0`. Introduce `k _`. Conclude with `zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))`.

Rewrite using `[hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hprod) hpos.ne', Real.log_prod hprod]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[Real.log_zpow]`.
-/
theorem log_h_torus (L : HermLine ι) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h (torusSmul c z)) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hsm : L.h (torusSmul c z) = (∏ k, ‖c k‖ ^ L.a k) * L.h z := L.smul c z hc
  have hpos : 0 < L.h z := L.pos z hz
  have hprod : ∀ k ∈ (Finset.univ : Finset K), ‖c k‖ ^ L.a k ≠ 0 := by
    intro k _
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hprod) hpos.ne', Real.log_prod hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_zpow]

/- English proof (translation)
Establish `hopen : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Establish `hset : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[hset]`.

Apply `isOpen_iInter_of_finite` to reduce the goal to its premises. Introduce `k`. Apply `isOpen_iUnion` to reduce the goal to its premises. Introduce `i`. Conclude with `isOpen_ne_fun (continuous_apply _) continuous_const`.

Establish `hh : ContDiffAt ℝ 2 L.h z`. Establish `h1` using `hL.contDiffAt (hopen.mem_nhds hz)`. Conclude with `h1.of_le (WithTop.coe_le_coe.mpr le_top)`. Conclude with `hh.log (L.pos z hz).ne'`.
-/
theorem contDiffAt_log_h {L : HermLine ι} (hL : IsSmoothHerm L) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) z := by
  have hopen : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have hset : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
        ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext w
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iUnion
    intro i
    exact isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ContDiffAt ℝ 2 L.h z := by
    have h1 := hL.contDiffAt (hopen.mem_nhds hz)
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hh.log (L.pos z hz).ne'

/- English proof (translation)
Take `⟨c, hc, h⟩` from `Re.R.compat x y y ⟨hy, Re.R.mem_U y⟩`. Establish `hz` using `(Re.R.mem y y (Re.R.mem_U y)).1`. Express the relevant statement in the definitionally equal form `Re.R.lift x y = torusSmul c _ at h`. Rewrite using `[h, log_h_torus _ c _ hc hz, log_h_torus _ c _ hc hz, Re.line_eq a t ht ht', Re.line_deg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_line_lift {D : ℕ} {σ : Type} {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (a : σ) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ S.t₀) (x y : Re.R.X) (hy : y ∈ Re.R.U x) :
    Real.log ((Re.line a t).h (Re.R.lift x y)) = Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y) := by
  obtain ⟨c, hc, h⟩ := Re.R.compat x y y ⟨hy, Re.R.mem_U y⟩
  have hz := (Re.R.mem y y (Re.R.mem_U y)).1
  change Re.R.lift x y = torusSmul c _ at h
  rw [h, log_h_torus _ c _ hc hz, log_h_torus _ c _ hc hz, Re.line_eq a t ht ht', Re.line_deg]
  ring

/- English proof (translation)
Use `set χ := Re.R.A.chart j with hχ`. Establish `hv0 : χ x ∈ χ.target` using `χ.map_source hj`. Establish `hχx : χ.symm (χ x) = x` using `χ.left_inv hj`. Take `⟨k, hk⟩` from `S.A.cover (Re.π x)`. Use `set ψ := S.A.chart k with hψ`.

Use `set Φ : S.X → ℝ := (PB.sumPot c fun a => S.potT a t).φ (Re.π x) with hΦd`. Establish `hΦ : ∀ w, Φ w = ∑ a, c a * ((S.th a).φ (Re.π x) w + S.phT a t w)` using `fun w => rfl`. Use `set τ : (Fin D → ℂ) → (Fin D → ℂ) := fun v => ψ (Re.π (χ.symm v)) with hτd`. Establish `hτv0 : τ (χ x) = ψ (Re.π x)` using `by simp only [hτd, hχx]`. Establish `hτ : AnalyticAt ℂ τ (χ x)`.

Apply `Re.holo.2 j k` to reduce the goal to its premises. Use `⟨hv0, ?_⟩` and prove the remaining obligations. Use `show Re.π (χ.symm (χ x)) ∈ ψ.source`. Rewrite using `[hχx]`. Conclude with `hk`.

Establish `hψx : ψ (Re.π x) ∈ ψ.target` using `ψ.map_source hk`. Establish `hψxl : ψ.symm (ψ (Re.π x)) = Re.π x` using `ψ.left_inv hk`. Establish `hΦsm : ContDiffAt ℝ 2 (Φ ∘ ψ.symm) (ψ (Re.π x))`. Establish `hfun : Φ ∘ ψ.symm = fun v => ∑ a, c a * ((S.th a).φ (Re.π x) (ψ.symm v) + S.phT a t (ψ.symm v))`. Use function extensionality and compare the values at `v`.

Conclude with `hΦ _`. Rewrite using `[hfun]`. Apply `ContDiffAt.sum` to reduce the goal to its premises. Introduce `a _`. Apply `ContDiffAt.mul contDiffAt_const` to reduce the goal to its premises.

Apply `ContDiffAt.add` to reduce the goal to its premises. Establish `h1` using `(S.sing a).1.1 (Re.π x) k`. Establish `hmem : ψ.target ∩ ψ.symm ⁻¹' (S.th a).U (Re.π x) ∈ 𝓝 (ψ (Re.π x))`. Apply `(ψ.isOpen_inter_preimage_symm ((S.th a).isOpen_U _)).mem_nhds` to reduce the goal to its premises. Use `⟨hψx, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_preimage, hψxl]`. Conclude with `(S.th a).mem_U _`. Conclude with `(h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)`. Establish `h1` using `((S.reg a).2.2 t ht ht').1 k`. Establish `hmem : ψ.target ∩ ψ.symm ⁻¹' Set.univ ∈ 𝓝 (ψ (Re.π x))`.

Rewrite using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `ψ.open_target.mem_nhds hψx`. Conclude with `(h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)`. Use `choose V hVo hxV G hG hGeq using fun a => Re.ref_pot a x (Set.mem_univ _)`. Use `set Gs : Re.R.X → ℂ := fun y => ∑ a, (c a : ℂ) * G a y with hGsum`.

Establish `hGsan : AnalyticAt ℂ (Gs ∘ χ.symm) (χ x)`. Establish `hfun : Gs ∘ χ.symm = fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v`. Use function extensionality and compare the values at `v`. Both sides reduce to the same expression. Establish `hfun2 : (fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v) = ∑ a, (fun v => (c a : ℂ) * (G a ∘ χ.symm) v)`.

Use function extensionality and compare the values at `v`. Simplify using `[Finset.sum_apply]`. Rewrite using `[hfun, hfun2]`. Apply `Finset.analyticAt_sum` to reduce the goal to its premises. Introduce `a _`.

Apply `analyticAt_const.mul` to reduce the goal to its premises. Apply `hG a j` to reduce the goal to its premises. Use `⟨hv0, ?_⟩` and prove the remaining obligations. Use `show χ.symm (χ x) ∈ V a`. Rewrite using `[hχx]`.

Conclude with `hxV a`. Establish `hcont : ContinuousAt χ.symm (χ x)` using `χ.continuousAt_symm hv0`. Establish `hev1 : ∀ᶠ v in 𝓝 (χ x), χ.symm v ∈ Re.R.U x`. Apply `hcont.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[hχx]`.

Conclude with `(Re.R.isOpen_U x).mem_nhds (Re.R.mem_U x)`. Establish `hev2 : ∀ᶠ v in 𝓝 (χ x), ∀ a, χ.symm v ∈ V a`. Rewrite using `[Filter.eventually_all]`. Introduce `a`. Apply `hcont.preimage_mem_nhds` to reduce the goal to its premises.

Rewrite using `[hχx]`. Conclude with `(hVo a).mem_nhds (hxV a)`. Establish `hev3 : ∀ᶠ v in 𝓝 (χ x), Re.π (χ.symm v) ∈ ψ.source`. Apply `(Re.holo.1.continuousAt.comp hcont).preimage_mem_nhds` to reduce the goal to its premises. Use `show ψ.source ∈ 𝓝 (Re.π (χ.symm (χ x)))`.

Rewrite using `[hχx]`. Conclude with `ψ.open_source.mem_nhds hk`. Establish `heq : (fun v => F (χ.symm v)) =ᶠ[𝓝 (χ x)] (fun v => ((Φ ∘ ψ.symm) ∘ τ) v + 1 * ((Gs ∘ χ.symm) v).re)` using `by filter_upwards [hev1, hev2, hev3] with v h1 h2 h3`. Establish `hl : ψ.symm (ψ (Re.π (χ.symm v))) = Re.π (χ.symm v)` using `ψ.left_inv h3`. Simplify using `only [Function.comp_apply, hτd, hl, hΦ, hGsum, one_mul, Complex.re_sum, Complex.re_ofReal_mul]`.

Rewrite using `[hF _ h1, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Establish `h` using `hGeq a (χ.symm v) (h2 a)`. Establish `h' : Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) - (S.th a).φ (Re.π x) (Re.π (χ.symm v)) = (G a (χ.symm v)).re` using `h`.

Rewrite using `[show Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) = (S.th a).φ (Re.π x) (Re.π (χ.symm v)) + (G a (χ.symm v)).re by linarith]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC1 : ContDiffAt ℝ 2 ((Φ ∘ ψ.symm) ∘ τ) (χ x)`. Apply `ContDiffAt.comp (χ x) (by rw [hτv0]; exact hΦsm)` to reduce the goal to its premises. Conclude with `hτ.contDiffAt.restrict_scalars ℝ`.

Establish `hC2 : ContDiffAt ℝ 2 (fun v => ((Gs ∘ χ.symm) v).re) (χ x)` using `Complex.reCLM.contDiff.contDiffAt.comp (χ x) (hGsan.contDiffAt.restrict_scalars ℝ)`. Establish `hmemP : ψ (Re.π x) ∈ ψ.target ∩ ψ.symm ⁻¹' (PB.sumPot c fun a => S.potT a t).U (Re.π x)`. Use `⟨hψx, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, hψxl]`. Conclude with `(PB.sumPot c fun a => S.potT a t).mem_U _`.

Establish `hnn` using `hpsh (Re.π x) k (ψ (Re.π x)) hmemP ((fderiv ℂ τ (χ x)) u)`. Rewrite using `[levi_congr heq u, levi_add_smul 1 hC1 hC2 u, levi_comp u hτ (by rw [hτv0]; exact hΦsm), levi_re_analytic hGsan u, hτv0]`. Simplify using `using hnn`.
-/
theorem levi_chart_nonneg {D : ℕ} {σ : Type} [Fintype σ] {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ S.t₀) (c : σ → ℝ) (hpsh : IsPsh S.A (PB.sumPot c fun a => S.potT a t))
    (x : Re.R.X) (F : Re.R.X → ℝ)
    (hF : ∀ y ∈ Re.R.U x, F y = ∑ a, c a * (Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y)))
    (j : Fin Re.R.A.n) (hj : x ∈ (Re.R.A.chart j).source) (u : Fin D → ℂ) :
    0 ≤ levi (fun v => F ((Re.R.A.chart j).symm v)) (Re.R.A.chart j x) u := by
  set χ := Re.R.A.chart j with hχ
  have hv0 : χ x ∈ χ.target := χ.map_source hj
  have hχx : χ.symm (χ x) = x := χ.left_inv hj
  obtain ⟨k, hk⟩ := S.A.cover (Re.π x)
  set ψ := S.A.chart k with hψ
  set Φ : S.X → ℝ := (PB.sumPot c fun a => S.potT a t).φ (Re.π x) with hΦd
  have hΦ : ∀ w, Φ w = ∑ a, c a * ((S.th a).φ (Re.π x) w + S.phT a t w) := fun w => rfl
  set τ : (Fin D → ℂ) → (Fin D → ℂ) := fun v => ψ (Re.π (χ.symm v)) with hτd
  have hτv0 : τ (χ x) = ψ (Re.π x) := by simp only [hτd, hχx]
  have hτ : AnalyticAt ℂ τ (χ x) := by
    apply Re.holo.2 j k
    refine ⟨hv0, ?_⟩
    show Re.π (χ.symm (χ x)) ∈ ψ.source
    rw [hχx]
    exact hk
  have hψx : ψ (Re.π x) ∈ ψ.target := ψ.map_source hk
  have hψxl : ψ.symm (ψ (Re.π x)) = Re.π x := ψ.left_inv hk
  have hΦsm : ContDiffAt ℝ 2 (Φ ∘ ψ.symm) (ψ (Re.π x)) := by
    have hfun : Φ ∘ ψ.symm = fun v => ∑ a, c a * ((S.th a).φ (Re.π x) (ψ.symm v) + S.phT a t (ψ.symm v)) := by
      funext v
      exact hΦ _
    rw [hfun]
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.add
    · have h1 := (S.sing a).1.1 (Re.π x) k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' (S.th a).U (Re.π x) ∈ 𝓝 (ψ (Re.π x)) := by
        apply (ψ.isOpen_inter_preimage_symm ((S.th a).isOpen_U _)).mem_nhds
        refine ⟨hψx, ?_⟩
        rw [Set.mem_preimage, hψxl]
        exact (S.th a).mem_U _
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
    · have h1 := ((S.reg a).2.2 t ht ht').1 k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' Set.univ ∈ 𝓝 (ψ (Re.π x)) := by
        rw [Set.preimage_univ, Set.inter_univ]
        exact ψ.open_target.mem_nhds hψx
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
  choose V hVo hxV G hG hGeq using fun a => Re.ref_pot a x (Set.mem_univ _)
  set Gs : Re.R.X → ℂ := fun y => ∑ a, (c a : ℂ) * G a y with hGsum
  have hGsan : AnalyticAt ℂ (Gs ∘ χ.symm) (χ x) := by
    have hfun : Gs ∘ χ.symm = fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v := by
      funext v
      rfl
    have hfun2 : (fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v) =
        ∑ a, (fun v => (c a : ℂ) * (G a ∘ χ.symm) v) := by
      funext v
      simp [Finset.sum_apply]
    rw [hfun, hfun2]
    apply Finset.analyticAt_sum
    intro a _
    apply analyticAt_const.mul
    apply hG a j
    refine ⟨hv0, ?_⟩
    show χ.symm (χ x) ∈ V a
    rw [hχx]
    exact hxV a
  have hcont : ContinuousAt χ.symm (χ x) := χ.continuousAt_symm hv0
  have hev1 : ∀ᶠ v in 𝓝 (χ x), χ.symm v ∈ Re.R.U x := by
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (Re.R.isOpen_U x).mem_nhds (Re.R.mem_U x)
  have hev2 : ∀ᶠ v in 𝓝 (χ x), ∀ a, χ.symm v ∈ V a := by
    rw [Filter.eventually_all]
    intro a
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (hVo a).mem_nhds (hxV a)
  have hev3 : ∀ᶠ v in 𝓝 (χ x), Re.π (χ.symm v) ∈ ψ.source := by
    apply (Re.holo.1.continuousAt.comp hcont).preimage_mem_nhds
    show ψ.source ∈ 𝓝 (Re.π (χ.symm (χ x)))
    rw [hχx]
    exact ψ.open_source.mem_nhds hk
  have heq : (fun v => F (χ.symm v)) =ᶠ[𝓝 (χ x)]
      (fun v => ((Φ ∘ ψ.symm) ∘ τ) v + 1 * ((Gs ∘ χ.symm) v).re) := by
    filter_upwards [hev1, hev2, hev3] with v h1 h2 h3
    have hl : ψ.symm (ψ (Re.π (χ.symm v))) = Re.π (χ.symm v) := ψ.left_inv h3
    simp only [Function.comp_apply, hτd, hl, hΦ, hGsum, one_mul, Complex.re_sum, Complex.re_ofReal_mul]
    rw [hF _ h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have h := hGeq a (χ.symm v) (h2 a)
    have h' : Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) - (S.th a).φ (Re.π x) (Re.π (χ.symm v)) =
        (G a (χ.symm v)).re := h
    rw [show Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) =
        (S.th a).φ (Re.π x) (Re.π (χ.symm v)) + (G a (χ.symm v)).re by linarith]
    ring
  have hC1 : ContDiffAt ℝ 2 ((Φ ∘ ψ.symm) ∘ τ) (χ x) := by
    apply ContDiffAt.comp (χ x) (by rw [hτv0]; exact hΦsm)
    exact hτ.contDiffAt.restrict_scalars ℝ
  have hC2 : ContDiffAt ℝ 2 (fun v => ((Gs ∘ χ.symm) v).re) (χ x) :=
    Complex.reCLM.contDiff.contDiffAt.comp (χ x) (hGsan.contDiffAt.restrict_scalars ℝ)
  have hmemP : ψ (Re.π x) ∈ ψ.target ∩ ψ.symm ⁻¹' (PB.sumPot c fun a => S.potT a t).U (Re.π x) := by
    refine ⟨hψx, ?_⟩
    rw [Set.mem_preimage, hψxl]
    exact (PB.sumPot c fun a => S.potT a t).mem_U _
  have hnn := hpsh (Re.π x) k (ψ (Re.π x)) hmemP ((fderiv ℂ τ (χ x)) u)
  rw [levi_congr heq u, levi_add_smul 1 hC1 hC2 u, levi_comp u hτ (by rw [hτv0]; exact hΦsm),
    levi_re_analytic hGsan u, hτv0]
  simpa using hnn

end RootFieldNumerics.Levi
