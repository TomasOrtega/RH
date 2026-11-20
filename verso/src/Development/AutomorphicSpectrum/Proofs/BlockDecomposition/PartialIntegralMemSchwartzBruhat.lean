import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

/- English proof (translation)
Take `⟨hF, hc⟩` from `mem_SB_iff.1 F.2`. Establish `hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ))` using `hc.isCompact.image continuous_snd`. Establish `hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)}`. Establish `h2 : IsLocallyConstant (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2))` using `hF.sub (hF.comp_continuous (by fun_prop))`. Establish `h3` using `h2.isOpen_fiber 0`.

Simplify `h3` using `[Set.preimage, sub_eq_zero]`. Take `⟨U, V, hU, -, haU, hKV, hUV⟩` from `generalized_tube_lemma (isCompact_singleton (x := a₀)) hK hopen (by`. Introduce and unpack `⟨a, b⟩ ⟨ha, -⟩`. Establish `ha' : a = a₀` using `ha`. Substitute `ha'` using the available equality.

Use the proof step `rfl)`. Use `filter_upwards [hU.mem_nhds (haU rfl)] with a ha b`. Distinguish the cases in `hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)`. Conclude with `hUV (Set.mk_mem_prod ha (hKV hb))`. Establish `h1 : (a, b) ∉ tsupport (F : A × B → ℂ)` using `fun h => hb ⟨_, h, rfl⟩`.

Establish `h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ)` using `fun h => hb ⟨_, h, rfl⟩`. Rewrite using `[image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]`.
-/
theorem eventually_slice_eq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by
  obtain ⟨hF, hc⟩ := mem_SB_iff.1 F.2
  have hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ)) := hc.isCompact.image continuous_snd
  have hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)} := by
    have h2 : IsLocallyConstant
        (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2)) :=
      hF.sub (hF.comp_continuous (by fun_prop))
    have h3 := h2.isOpen_fiber 0
    simpa [Set.preimage, sub_eq_zero] using h3
  obtain ⟨U, V, hU, -, haU, hKV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := a₀)) hK
    hopen (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = a₀ := ha
      subst ha'
      rfl)
  filter_upwards [hU.mem_nhds (haU rfl)] with a ha b
  by_cases hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)
  · exact hUV (Set.mk_mem_prod ha (hKV hb))
  · have h1 : (a, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    have h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ _ _ _ μ _ w _ F`. Take `⟨-, hc⟩` from `mem_SB_iff.1 F.2`. Use `mem_SB_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `a₀`.

Use `filter_upwards [eventually_slice_eq F a₀] with a ha`. Simplify using `only [ha]`. Use `HasCompactSupport.intro (hc.isCompact.image continuous_fst) ?_` and prove the remaining obligations. Introduce `a ha`. Establish `h0 : ∀ b, (F : A × B → ℂ) (a, b) = 0` using `fun b => image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩`.

Simplify using `only [h0, zero_mul, integral_zero]`.
-/
theorem integral_mem_SB : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
    [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B)
    [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B),
    (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  intro A B _ _ _ _ _ _ _ _ _ _ μ _ w _ F
  obtain ⟨-, hc⟩ := mem_SB_iff.1 F.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    filter_upwards [eventually_slice_eq F a₀] with a ha
    simp only [ha]
  · refine HasCompactSupport.intro (hc.isCompact.image continuous_fst) ?_
    intro a ha
    have h0 : ∀ b, (F : A × B → ℂ) (a, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
    simp only [h0, zero_mul, integral_zero]

end GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
