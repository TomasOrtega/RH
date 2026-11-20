import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Tow

section Gen

/- English proof (translation)
Rewrite using `[h𝓕.measure_eq_tsum K]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨g, hg, hgK⟩` from `hK y`. Use `⟨⟨-g, neg_mem hg⟩, ?_, hy⟩` and prove the remaining obligations. Use `⟨g + y, hgK, ?_⟩` and prove the remaining obligations.

Use `show -g + (g + y) = y`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨_, _, hy⟩`. Conclude with `hy`. Use `_ ≤ ∑' g : Λ, μ ((g +ᵥ K) ∩ 𝓕) := measure_iUnion_le _`.
-/
theorem fd_measure_le_of_cover {V : Type*} [AddCommGroup V] [MeasurableSpace V] {μ : Measure V}
    {Λ : AddSubgroup V} [Countable Λ] [MeasurableConstVAdd Λ V] [VAddInvariantMeasure Λ V μ] {𝓕 : Set V}
    (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {K : Set V}
    (hK : ∀ y, ∃ g ∈ Λ, g + y ∈ K) : μ 𝓕 ≤ μ K := by
  rw [h𝓕.measure_eq_tsum K]
  calc μ 𝓕 = μ (⋃ g : Λ, (g +ᵥ K) ∩ 𝓕) := by
        congr 1
        ext y
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hy
          obtain ⟨g, hg, hgK⟩ := hK y
          refine ⟨⟨-g, neg_mem hg⟩, ?_, hy⟩
          refine ⟨g + y, hgK, ?_⟩
          show -g + (g + y) = y
          abel
        · rintro ⟨_, _, hy⟩; exact hy
    _ ≤ ∑' g : Λ, μ ((g +ᵥ K) ∩ 𝓕) := measure_iUnion_le _

/- English proof (translation)
The claim follows from `(fd_measure_le_of_cover h𝓕 hK).trans_lt hKc.measure_lt_top`.
-/
theorem fd_measure_lt_top {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] {μ : Measure V}
    [IsFiniteMeasureOnCompacts μ] {Λ : AddSubgroup V} [Countable Λ] [MeasurableConstVAdd Λ V]
    [VAddInvariantMeasure Λ V μ] {𝓕 : Set V} (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {K : Set V} (hKc : IsCompact K)
    (hK : ∀ y, ∃ g ∈ Λ, g + y ∈ K) : μ 𝓕 < ⊤ :=
  (fd_measure_le_of_cover h𝓕 hK).trans_lt hKc.measure_lt_top

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ] {𝓕 : Set V}

/- English proof (translation)
Establish `hmp` using `measurePreserving_add_right μ a`. Establish `hemb : MeasurableEmbedding (fun x : V => x + a)` using `measurableEmbedding_addRight a`. Rewrite using `[← hmp.setIntegral_image_emb hemb f 𝓕]`. Establish `himg : (fun x : V => x + a) '' 𝓕 = a +ᵥ 𝓕`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, add_comm a x⟩`. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x, hx, add_comm x a⟩`. Rewrite using `[himg]`. Conclude with `(h𝓕.vadd_of_comm a).setIntegral_eq h𝓕 (fun g x => hf g g.2 x)`.
-/
theorem fd_setIntegral_add (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {f : V → ℂ}
    (hf : ∀ g ∈ Λ, ∀ x, f (g + x) = f x) (a : V) :
    ∫ x in 𝓕, f (x + a) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have hmp := measurePreserving_add_right μ a
  have hemb : MeasurableEmbedding (fun x : V => x + a) := measurableEmbedding_addRight a
  rw [← hmp.setIntegral_image_emb hemb f 𝓕]
  have himg : (fun x : V => x + a) '' 𝓕 = a +ᵥ 𝓕 := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, add_comm a x⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, add_comm x a⟩
  rw [himg]
  exact (h𝓕.vadd_of_comm a).setIntegral_eq h𝓕 (fun g x => hf g g.2 x)

/- English proof (translation)
Establish `hper : ∀ g ∈ Λ, ∀ x, χ (g + x) = χ x` using `fun g hg x => by rw [hmul, hΛ g hg, one_mul]`. Establish `h` using `fd_setIntegral_add h𝓕 hper a`. Rewrite `h` using `[hmul]`. Rewrite `h` using `[integral_mul_const]`. Establish `: (∫ x in 𝓕, χ x ∂μ) * (χ a - 1) = 0` using `by rw [mul_sub, mul_one, h, sub_self]`.

Break down `mul_eq_zero.1 this with h0 | h0` into its components or cases. Conclude with `h0`. Conclude with `absurd (sub_eq_zero.1 h0) ha`.
-/
theorem fd_setIntegral_char_eq_zero (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {χ : V → ℂ}
    (hmul : ∀ x y, χ (x + y) = χ x * χ y) (hΛ : ∀ g ∈ Λ, χ g = 1) {a : V} (ha : χ a ≠ 1) :
    ∫ x in 𝓕, χ x ∂μ = 0 := by
  have hper : ∀ g ∈ Λ, ∀ x, χ (g + x) = χ x := fun g hg x => by rw [hmul, hΛ g hg, one_mul]
  have h := fd_setIntegral_add h𝓕 hper a
  simp_rw [hmul] at h
  rw [integral_mul_const] at h
  have : (∫ x in 𝓕, χ x ∂μ) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0) ha

end Gen

section FDom

end FDom

section Cent

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable (F : Type) [Field F] [NumberField F]

def ratV (r : ℕ) : AddSubgroup (Fin r → AF F) :=
  (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom (Fin r)).range

end Cent

section Frame

open Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

end Frame

end Formalism.IndefR.Tow

end
