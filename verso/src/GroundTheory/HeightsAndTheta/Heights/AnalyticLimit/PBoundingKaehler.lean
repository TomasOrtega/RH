import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Establish `hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y` using `((hP.1 x k).of_le two_le_smooth_kb).contDiffAt (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target (P.isOpen_U x)).mem_nhds hy)`. Establish `h` using `levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w`. Establish `he : (P.rsmul a).φ x ∘ (A.chart k).symm = fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z`. Use function extensionality and compare the values at `z`. Simplify using `[LocPot.rsmul]`.

Rewrite using `[he, h, levi_const, zero_add]`.
-/
theorem levi_rsmul_chart (A : FinHolAtlas D X) (P : LocPot X) (hP : IsPotential A P) (a : ℝ)
    (x : X) (k : Fin A.n) (y : Fin D → ℂ)
    (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) (w : Fin D → ℂ) :
    levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w = a * levi (P.φ x ∘ (A.chart k).symm) y w := by
  have hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y :=
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w
  have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
      fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [he, h, levi_const, zero_add]

/- English proof (translation)
Introduce `X _ _ _ D A om m th hth`. Establish `hX : IsCompact (Set.univ : Set X)` using `isCompact_univ`. Use `choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos`. Use `set K : ℝ := 1 + ∑ i, M i with hKdef`. Establish `hsum : 0 ≤ ∑ i, M i` using `Finset.sum_nonneg fun i _ => hM0 i`.

Establish `hK : 0 < K` using `by linarith`. Establish `hMK : ∀ i, M i ≤ K` using `fun i => by`. Use `Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ, 0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w`.

Introduce `x k y hy w`. Break down `eq_or_ne w 0 with h0 | h0` into its components or cases. Rewrite using `[h0, levi_zero]`. Conclude with `(om.pos x k y hy w h0).le`. Use `⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot, fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[levi_rsmul_chart A om.pot om.isPot K x k y hy w]`. Conclude with `mul_pos hK (om.pos x k y hy w hw)`. Introduce `x k y hy w`. Establish `hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x` using `⟨hy.1, hy.2.2⟩`. Establish `hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x)` using `⟨hy.1, hy.2.1.2, hy.2.2⟩`.

Rewrite using `[levi_rsmul_chart A om.pot om.isPot K x k y hyo w]`. Establish `h1` using `abs_le.mp (hM i x k y hyb w)`. Establish `h2` using `hnn x k y hyo w`. Establish `h3` using `hMK i`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `x k y hy w`. Establish `hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x` using `⟨hy.1, hy.2.1.2⟩`. Establish `hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x)` using `⟨hy.1, hy.2.2, hy.2.1.2⟩`. Rewrite using `[levi_rsmul_chart A om.pot om.isPot K x k y hyo w]`. Establish `h1` using `abs_le.mp (hM i x k y hyb w)`.

Establish `h2` using `hnn x k y hyo w`. Establish `h3` using `hMK i`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem BoundingKaehler.proof : BoundingKaehler.Statement := by
  intro X _ _ _ D A om m th hth
  have hX : IsCompact (Set.univ : Set X) := isCompact_univ
  choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos
  set K : ℝ := 1 + ∑ i, M i with hKdef
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  have hK : 0 < K := by linarith
  have hMK : ∀ i, M i ≤ K := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)
    linarith
  have hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ,
      0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (om.pos x k y hy w h0).le
  refine ⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot,
    fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [levi_rsmul_chart A om.pot om.isPot K x k y hy w]
    exact mul_pos hK (om.pos x k y hy w hw)
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.1.2, hy.2.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.1.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.2, hy.2.1.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
