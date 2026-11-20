import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A U z hE`. Apply `IsLocalHomeomorph.mk` to reduce the goal to its premises. Introduce `y`. Use `set i := A.pick y`. Use `set e := A.chart i`.

Use `set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef`. Establish `hS : IsOpen S` using `e.isOpen_inter_preimage_symm hE.isOpen`. Establish `hyU : (y : Y) ∈ U` using `y.2`. Establish `hys : (y : Y) ∈ e.source` using `A.mem_pick y`. Establish `hxS : e y ∈ S` using `⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩`.

Establish `hd : DifferentiableOn ℂ (z ∘ e.symm) S` using `hE.holo i`. Establish `hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S` using `contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS ((differentiableOn_piLp 2).1 hd k))`. Establish `hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y)` using `hcd.contDiffAt (hS.mem_nhds hxS)`. Establish `hst` using `hca.hasStrictFDerivAt (by simp)`. Establish `hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0` using `hE.det_ne i y hyU hys`.

Set `L : V n ≃L[ℂ] V n` to `(LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv`. Establish `hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y)`. Use extensionality with `v`. Both sides reduce to the same expression. Establish `hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y)` using `hL ▸ hst`.

Set `h` to `hst'.toOpenPartialHomeomorph (z ∘ e.symm)`. Set `P` to `e.trans (h.restrOpen S hS)`. Establish `hyP : (y : Y) ∈ P.source`. Simplify using `only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source, Set.mem_inter_iff, Set.mem_preimage]`. Conclude with `⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩`.

Establish `hPz : ∀ w ∈ P.source, P w = z w`. Introduce `w hw`. Establish `hw1 : w ∈ e.source`. Simplify using `only [P, OpenPartialHomeomorph.trans_source] at hw`. Conclude with `hw.1`.

Establish `hh : ∀ v, h v = (z ∘ e.symm) v` using `fun v => by`. Simplify using `only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`. Express the relevant statement in the definitionally equal form `(h.restrOpen S hS) (e w) = z w`. Express the relevant statement in the definitionally equal form `h (e w) = z w`. Rewrite using `[hh, Function.comp_apply, e.left_inv hw1]`.

Establish `hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y)` using `⟨y⟩`. Set `Q` to `P.subtypeRestr hne`. Use `⟨Q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[OpenPartialHomeomorph.subtypeRestr_source]`. Conclude with `hyP`.

Introduce `w hw`. Rewrite `hw` using `[OpenPartialHomeomorph.subtypeRestr_source]`. Rewrite using `[OpenPartialHomeomorph.subtypeRestr_coe]`. Conclude with `(hPz w hw).symm`.
-/
theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
