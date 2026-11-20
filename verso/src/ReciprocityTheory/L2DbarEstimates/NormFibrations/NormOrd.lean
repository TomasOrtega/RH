import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormOrdStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ) (x : M) (m : ℕ),
    IsLocalHomeomorph z → Holo n z f → VanishesBeyond n z f x m →
    Norm.VanishOrder n z f x (m + 1)

/- English proof (translation)
Introduce `n M _ z f x m hz hf hv`. Take `⟨e, he, hx⟩` from `exists_chart n z hz x`. Establish `hzx : z x ∈ e.target` using `by rw [he hx]; exact e.map_source hx`. Take `⟨C, hC⟩` from `Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x) e.open_target hzx (hf e he) m (hv e he hx)`. Establish `h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1)` using `hz.continuous.continuousAt.tendsto.eventually hC`.

Establish `h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source` using `e.open_source.mem_nhds hx`. Rewrite using `[Norm.VanishOrder, Asymptotics.isBigO_iff]`. Use `⟨C, ?_⟩` and prove the remaining obligations. Use `filter_upwards [h1, h2] with y hy hys`. Establish `hy' : e.symm (z y) = y` using `by rw [he hys]; exact e.left_inv hys`.

Simplify using `only [Function.comp_apply, hy'] at hy`. Rewrite using `[norm_pow, norm_norm]`. Conclude with `hy`.
-/
theorem normOrd : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy

end ReciprocityTheory.L2DbarEstimates
