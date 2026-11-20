import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf

open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open MeasureTheory
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LU

/- English proof (translation)
Introduce `F _ _ _ _ _ _ g hg`. Establish `hmeas : Measurable (fun a : Fˣ => g (ord (a : F)))`. Establish `hord : Measurable (fun a : Fˣ => ord (a : F))` using `measurable_to_countable' fun k => measurableSet_ordShell (K := F) k`. Conclude with `(Measurable.of_discrete (f := g)).comp hord`. Establish `hfin : ∑' k, ‖g k‖ₑ ≠ ⊤`.

Repeatedly rewrite using `[← ofReal_norm]`. Conclude with `hg.tsum_ofReal_ne_top`. Establish `hI : Integrable (fun a : Fˣ => g (ord (a : F))) (multHaar F)`. Use `⟨hmeas.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hle` using `lintegral_multHaar_le_tsum (K := F) (fun u => ‖g (ord (u : F))‖ₑ) (fun k => ‖g k‖ₑ) (fun _ => le_rfl)`.

Conclude with `lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `hs` using `hasSum_setIntegral_ordShell hI`. Establish `hk : ∀ k : ℤ, ∫ u in ordShell F k, g (ord (u : F)) ∂multHaar F = g k`. Introduce `k`.

Establish `hc : Set.EqOn (fun u : Fˣ => g (ord (u : F))) (fun _ => g k) (ordShell F k)` using `fun u hu => by simp only [mem_ordShell.mp hu]`. Rewrite using `[setIntegral_congr_fun (measurableSet_ordShell k) hc, setIntegral_const, measureReal_def, multHaar_ordShell]`. Simplify using the standard rewrite rules. Simplify using `only [hk] at hs`. Conclude with `hs.tsum_eq.symm`.
-/
theorem sShell : Ad3.LU.SShell := by
  intro F _ _ _ _ _ _ g hg
  have hmeas : Measurable (fun a : Fˣ => g (ord (a : F))) := by
    have hord : Measurable (fun a : Fˣ => ord (a : F)) :=
      measurable_to_countable' fun k => measurableSet_ordShell (K := F) k
    exact (Measurable.of_discrete (f := g)).comp hord
  have hfin : ∑' k, ‖g k‖ₑ ≠ ⊤ := by
    simp_rw [← ofReal_norm]
    exact hg.tsum_ofReal_ne_top
  have hI : Integrable (fun a : Fˣ => g (ord (a : F))) (multHaar F) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hle := lintegral_multHaar_le_tsum (K := F) (fun u => ‖g (ord (u : F))‖ₑ)
      (fun k => ‖g k‖ₑ) (fun _ => le_rfl)
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
  refine ⟨hI, ?_⟩
  have hs := hasSum_setIntegral_ordShell hI
  have hk : ∀ k : ℤ, ∫ u in ordShell F k, g (ord (u : F)) ∂multHaar F = g k := by
    intro k
    have hc : Set.EqOn (fun u : Fˣ => g (ord (u : F))) (fun _ => g k) (ordShell F k) :=
      fun u hu => by simp only [mem_ordShell.mp hu]
    rw [setIntegral_congr_fun (measurableSet_ordShell k) hc, setIntegral_const, measureReal_def,
      multHaar_ordShell]
    simp
  simp only [hk] at hs
  exact hs.tsum_eq.symm

end GlobalTheory.CompanionTheory.LU
