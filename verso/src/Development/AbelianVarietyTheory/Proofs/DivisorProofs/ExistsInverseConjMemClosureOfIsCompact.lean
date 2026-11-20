import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ _ _ _ H C hC g hW`. Set `K : Set (X × X)` to `(C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}`. Establish `hK : IsCompact K`. Use `(hC.prod hC).inter_right ?_` and prove the remaining obligations. Conclude with `(isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hcont : Continuous fun z : X × (X × X) => z.2.1 * z.1 * z.2.2` using `((continuous_snd.fst).mul continuous_fst).mul continuous_snd.snd`. Establish `hP : ∀ y ∈ K, ∀ᶠ z : X × (X × X) in 𝓝 (g, y), z.2.1 * z.1 * z.2.2 ∈ (closure H)ᶜ`. Introduce `y hy`.

Apply `hcont.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Apply `isClosed_closure.isOpen_compl.mem_nhds` to reduce the goal to its premises. Conclude with `hne y.1 hy.1.1 y.2 hy.1.2 hy.2.1 hy.2.2`. Establish `hev` using `hK.eventually_forall_of_forall_eventually (x₀ := g) (P := fun w (y : X × X) => y.1 * w * y.2 ∈ (closure H)ᶜ) hP`. Take `⟨c, hc, c', hc', h1, h2, w, hw, hH⟩` from `hW _ hev`.

Conclude with `hw (c, c') ⟨⟨hc, hc'⟩, h1, h2⟩ (subset_closure hH)`.
-/
theorem exists_inverse_conj_mem_closure_of_isCompact :
    ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X),
      IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧
        ∃ w ∈ W, c * w * c' ∈ H) →
      ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  intro X _ _ _ _ H C hC g hW
  let K : Set (X × X) := (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hK : IsCompact K := by
    refine (hC.prod hC).inter_right ?_
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  by_contra hne
  push_neg at hne
  have hcont : Continuous fun z : X × (X × X) => z.2.1 * z.1 * z.2.2 :=
    ((continuous_snd.fst).mul continuous_fst).mul continuous_snd.snd
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (X × X) in 𝓝 (g, y), z.2.1 * z.1 * z.2.2 ∈ (closure H)ᶜ := by
    intro y hy
    apply hcont.continuousAt.preimage_mem_nhds
    apply isClosed_closure.isOpen_compl.mem_nhds
    exact hne y.1 hy.1.1 y.2 hy.1.2 hy.2.1 hy.2.2
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := g)
    (P := fun w (y : X × X) => y.1 * w * y.2 ∈ (closure H)ᶜ) hP
  obtain ⟨c, hc, c', hc', h1, h2, w, hw, hH⟩ := hW _ hev
  exact hw (c, c') ⟨⟨hc, hc'⟩, h1, h2⟩ (subset_closure hH)

end GlobalTheory
