import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CosetSumApply

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

/- English proof (translation)
Take `⟨γ, hγc, hγ0, hγadd, hγe⟩` from `hC n Z b`. Take `⟨Cd, hCd0, hR⟩` from `hF n m e (z - s₀) Z b`. Use `choose Rf hRf using hR`. Establish `hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀) (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) = fz m e (z - s₀) (mR (y₁ * γ s))`. Introduce `y₁ s`.

Rewrite using `[mR_mul, hγe]`. Establish `hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀) (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s`. Introduce `y₁ s`. Establish `h1` using `HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)`. Establish `hfe : (fun u : ℝ => fz m e (z - s₀) (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) = fun x : ℝ => fz m e (z - s₀) (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))`.

Use function extensionality and compare the values at `u`. Rewrite using `[hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]`. Rewrite using `[hfe]`. Conclude with `h1`. Establish `hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1)` using `isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))`.

Take `⟨u, hu, hbound⟩` from `(h.far z hz).1 _ hK`. Establish `hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 → ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q`. Introduce `q s hs`. Establish `hb` using `hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q`. Rewrite using `[mul_assoc (y₀ q), ← hyC q (y * γ s)]`.

Simplify `hb` using `only [GlobalTheory.Eis.term, trm, mul_assoc]`. Establish `hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q`. Introduce `q s hs`. Establish `h1` using `(hRf (y₀ q * y * γ s)).2`. Establish `h2` using `hterm q s (Ioo_subset_Icc_self hs)`.

Rewrite `h2`, the goal using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1` using `⟨by norm_num, by norm_num⟩`. Establish `hg0 : Summable (fun q => C q * fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))))` using `hu.of_norm_bounded fun q => by`. Simplify `hterm q 0 ⟨by norm_num, by norm_num⟩` using `only [hfzγ]`.

Establish `hsum` using `hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo (g := fun q (s : ℝ) => C q * fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) (g' := fun q s => C q * Rf (y₀ q * y * γ s)) (fun q s _ => (hderiv (y₀ q * y …`. Rewrite `hsum` using `[hγ0]`. Simplify using `only [mul_one] at hsum`. Establish `hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y)` using `fun q => (hRf (y₀ q * y)).1.deriv`. Establish `hfun : (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) = fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))`.

Use function extensionality and compare the values at `s`. Establish `hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) = Ê z (g * ι (y * γ s))`. Rewrite using `[← hγe, ← mR_mul, resG_mR]`. Rewrite using `[hl, (h.far z hz).2]`. Simplify using `only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]`.

Use `congr 1`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]`. Simplify using `only [hRfd]`. Use `⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩` and prove the remaining obligations.

Simplify `hbd q 0 h0mem` using `only [hγ0, mul_one]`. Rewrite using `[hfun, (hsum.const_mul (d.eval z)).deriv]`.
-/
theorem dirSeries (hC : CurveGR) (hF : FzDer) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) {z : ℂ} (hz : t < z.re)
    (Z : M2 n) (b : Bool) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0) ∧
    deriv (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 =
      d.eval z * ∑' q, C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 := by
  obtain ⟨γ, hγc, hγ0, hγadd, hγe⟩ := hC n Z b
  obtain ⟨Cd, hCd0, hR⟩ := hF n m e (z - s₀) Z b
  choose Rf hRf using hR
  have hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
      fz m e (z - s₀) (mR (y₁ * γ s)) := by
    intro y₁ s
    rw [mR_mul, hγe]
  have hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s := by
    intro y₁ s
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)
    have hfe : (fun u : ℝ => fz m e (z - s₀)
        (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) =
        fun x : ℝ => fz m e (z - s₀)
          (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))) := by
      funext u
      rw [hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]
    rw [hfe]
    exact h1
  have hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))
  obtain ⟨u, hu, hbound⟩ := (h.far z hz).1 _ hK
  have hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q := by
    intro q s hs
    have hb := hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q
    rw [mul_assoc (y₀ q), ← hyC q (y * γ s)]
    simpa only [GlobalTheory.Eis.term, trm, mul_assoc] using hb
  have hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q := by
    intro q s hs
    have h1 := (hRf (y₀ q * y * γ s)).2
    have h2 := hterm q s (Ioo_subset_Icc_self hs)
    rw [norm_mul] at h2 ⊢
    calc ‖C q‖ * ‖Rf (y₀ q * y * γ s)‖
        ≤ ‖C q‖ * (Cd * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cd * (‖C q‖ * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) := by ring
      _ ≤ Cd * u q := mul_le_mul_of_nonneg_left h2 hCd0
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun q => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))) :=
    hu.of_norm_bounded fun q => by
      simpa only [hfzγ] using hterm q 0 ⟨by norm_num, by norm_num⟩
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo
    (g := fun q (s : ℝ) => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))))
    (g' := fun q s => C q * Rf (y₀ q * y * γ s))
    (fun q s _ => (hderiv (y₀ q * y) s).const_mul (C q)) hbd h0mem hg0 h0mem
  rw [hγ0] at hsum
  simp only [mul_one] at hsum
  have hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y) :=
    fun q => (hRf (y₀ q * y)).1.deriv
  have hfun : (fun s : ℝ => resG ι (Ê z) g
      (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) =
      fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) := by
    funext s
    have hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
        Ê z (g * ι (y * γ s)) := by
      rw [← hγe, ← mR_mul, resG_mR]
    rw [hl, (h.far z hz).2]
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]
  simp only [hRfd]
  refine ⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩
  · simpa only [hγ0, mul_one] using hbd q 0 h0mem
  · rw [hfun, (hsum.const_mul (d.eval z)).deriv]

end PositivityTheory.Rg.Sw.HSt.FarP
