import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

/- English proof (translation)
Establish `hpos : 0 < Real.sqrt (c.toReal + 1)` using `Real.sqrt_pos.2 (by positivity)`. Use `⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩` and prove the remaining obligations. Establish `hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1)` using `(div_pos hε hpos).le`. Rewrite using `[← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]`. Establish `hct : c = ENNReal.ofReal c.toReal` using `(ENNReal.ofReal_toReal hc).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hct]`. Use `_ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by`. Rewrite using `[ENNReal.ofReal_mul (by positivity)]`. Use `_ ≤ ENNReal.ofReal (ε ^ 2) := ?_`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1` using `Real.sq_sqrt (by positivity)`. Rewrite using `[div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Establish `: 0 ≤ ε ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith

/- English proof (translation)
Introduce `X ι _ Φ T y j k ε hΦ hT hk hε`. Take `⟨N, hNc, hN1⟩` from `exists_compact_mem_nhds (1 : X.G)`. Establish `h1N : (1 : X.G) ∈ N` using `mem_of_mem_nhds hN1`. Use `set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀`. Establish `hΩ₀c : IsCompact Ω₀` using `isCompact_iUnion fun l => (hΦ l j).2.isCompact`.

Use `set Ω : Set X.G := Ω₀ * N with hΩ`. Establish `hΩc : IsCompact Ω` using `hΩ₀c.mul hNc`. Use `set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc`. Establish `hctop : c ≠ ⊤`. Use `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)` and prove the remaining obligations.

Conclude with `hΩc.inv.measure_lt_top.ne`. Conclude with `(hCnt X).1 _ (hΩc.inv.mul hΩc) y`. Take `⟨δ, hδ, hδc⟩` from `exists_delta c hctop ε hε`. Use `choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ`. Use `⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩` and prove the remaining obligations.

Introduce `ψ hψ hsupp u hu`. Establish `hsN : tsupport ψ ⊆ N` using `hsupp.trans Set.inter_subset_left`. Establish `hsl : ∀ l, tsupport ψ ⊆ Wl l` using `fun l => hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))`. Establish `hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u)` using `fun l => (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)`. Establish `hfin` using `hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by`.

Establish `hcv` using `hCv X (Φ l j) ψ (hΦ l j) hψ.1`. Use `⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩` and prove the remaining obligations. Conclude with `hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)`. Introduce `z hz`. Conclude with `⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)`.

Use `hvec hk`. Establish `hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2`. Use `hfin.trans (le_trans (le_of_eq ?_) hδc)` and prove the remaining obligations. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε` using `(ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle`. Rewrite `hle'` using `[← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le]`. Conclude with `hle'`.
-/
theorem vecLim_of (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'

end GlobalTheory.CompanionTheory.KernelColumns

end
