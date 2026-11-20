import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Bump

/- English proof (translation)
Introduce `X W hW`. Take `⟨N, hNn, hNW, hNc⟩` from `local_compact_nhds hW`. Establish `h1 : (1 : X.G) ∈ interior N` using `mem_interior_iff_mem_nhds.mpr hNn`. Take `⟨b, hb1, hb0, hbc, hbI⟩` from `exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl (Set.disjoint_singleton_left.mpr (fun h => h h1))`. Establish `hbnn : ∀ z, 0 ≤ b z` using `fun z => (hbI z).1`.

Establish `hb11 : b 1 = 1` using `hb1 (Set.mem_singleton _)`. Establish `hsupp : Function.support b ⊆ N`. Introduce `x hx`. Assume the negation of the conclusion as `hxN`. Conclude with `hx (hb0 (fun hi => hxN (interior_subset hi)))`.

Establish `hts : tsupport b ⊆ N` using `closure_minimal hsupp hNc.isClosed`. Establish `hcc : Continuous fun z : X.G => b z⁻¹` using `b.continuous.comp continuous_inv`. Establish `hcs : HasCompactSupport fun z : X.G => b z⁻¹` using `hbc.comp_homeomorph (Homeomorph.inv X.G)`. Establish `hI : 0 < ∫ z, b z⁻¹ ∂X.μ` using `hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _) (x := 1) (by simp [hb11])`. Use `set I := ∫ z, b z⁻¹ ∂X.μ with hIdef`.

Establish `hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I` using `fun z => by`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]`. Establish `hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b`. Introduce `x hx h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `[h0]`. Use `⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Complex.continuous_ofReal.comp (b.continuous.div_const I)`. Conclude with `hbc.mono hsub`. Introduce `z`.

Simplify using `only [hnorm]`. Simplify using `only [hnorm]`. Rewrite using `[integral_div, ← hIdef, div_self hI.ne']`. Conclude with `(closure_mono hsub).trans (hts.trans hNW)`.
-/
theorem bumpEx : BumpEx := by
  intro X W hW
  obtain ⟨N, hNn, hNW, hNc⟩ := local_compact_nhds hW
  have h1 : (1 : X.G) ∈ interior N := mem_interior_iff_mem_nhds.mpr hNn
  obtain ⟨b, hb1, hb0, hbc, hbI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1))
  have hbnn : ∀ z, 0 ≤ b z := fun z => (hbI z).1
  have hb11 : b 1 = 1 := hb1 (Set.mem_singleton _)
  have hsupp : Function.support b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hb0 (fun hi => hxN (interior_subset hi)))
  have hts : tsupport b ⊆ N := closure_minimal hsupp hNc.isClosed
  have hcc : Continuous fun z : X.G => b z⁻¹ := b.continuous.comp continuous_inv
  have hcs : HasCompactSupport fun z : X.G => b z⁻¹ :=
    hbc.comp_homeomorph (Homeomorph.inv X.G)
  have hI : 0 < ∫ z, b z⁻¹ ∂X.μ :=
    hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _)
      (x := 1) (by simp [hb11])
  set I := ∫ z, b z⁻¹ ∂X.μ with hIdef
  have hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]
  have hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b := by
    intro x hx h0
    apply hx
    simp [h0]
  refine ⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (b.continuous.div_const I)
  · exact hbc.mono hsub
  · intro z
    simp only [hnorm]
  · simp only [hnorm]
    rw [integral_div, ← hIdef, div_self hI.ne']
  · exact (closure_mono hsub).trans (hts.trans hNW)

end GlobalTheory.CompanionTheory.Bump
