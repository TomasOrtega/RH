import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7}

def VolPairEx (V : HSp D) : Prop := ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2

/- English proof (translation)
Unfold `volPair`. Conclude with `dif_pos h`.
-/
theorem volPair_eq_choose (V : HSp D) (h : VolPairEx V) : volPair V = h.choose := by
  unfold volPair
  exact dif_pos h

/- English proof (translation)
Rewrite using `[volPair_eq_choose V h]`. Conclude with `h.choose_spec`.
-/
theorem volPair_isVolPair (V : HSp D) (h : VolPairEx V) : IsVolPair D V (volPair V).1 (volPair V).2 := by
  rw [volPair_eq_choose V h]
  exact h.choose_spec

/- English proof (translation)
Take `⟨⟨μ, hμ⟩, hall⟩` from `h V hs`. Take `⟨⟨𝓕, h𝓕⟩, _⟩` from `hall μ hμ`. Conclude with `⟨(μ, 𝓕), hμ, h𝓕⟩`.
-/
theorem isVolPair_of_volTie (h : VolTieG D) (V : HSp D) (hs : V.SigOK) : VolPairEx V := by
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h V hs
  obtain ⟨⟨𝓕, h𝓕⟩, _⟩ := hall μ hμ
  exact ⟨(μ, 𝓕), hμ, h𝓕⟩

/- English proof (translation)
Take `⟨hμ, h𝓕⟩` from `hp`. Conclude with `((h V hs).2 μ hμ).2 𝓕 h𝓕`.
-/
theorem mass_eq_of_isVolPair (h : VolTieG D) (V : HSp D) (hs : V.SigOK) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hp : IsVolPair D V μ 𝓕) : μ 𝓕 = ENNReal.ofReal (D.vol V) := by
  obtain ⟨hμ, h𝓕⟩ := hp
  exact ((h V hs).2 μ hμ).2 𝓕 h𝓕

/- English proof (translation)
Use `first`. Consider the case `exact measurable_quotient_mk'`. Consider the case `exact fun _ hs => hs`.
-/
theorem autMk_measurable (V : HSp D) : Measurable (autMk V) := by
  first
  | exact measurable_quotient_mk'
  | exact fun _ hs => hs

/- English proof (translation)
Unfold `muQ`. Rewrite using `[Measure.map_apply (autMk_measurable V) MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]`.
-/
theorem muQ_univ (V : HSp D) : muQ V Set.univ = (volPair V).1 (volPair V).2 := by
  unfold muQ
  rw [Measure.map_apply (autMk_measurable V) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

/- English proof (translation)
Rewrite using `[muQ_univ]`. Conclude with `mass_eq_of_isVolPair h V hs (volPair_isVolPair V (isVolPair_of_volTie h V hs))`.
-/
theorem muQ_univ_eq_vol (h : VolTieG D) (V : HSp D) (hs : V.SigOK) :
    muQ V Set.univ = ENNReal.ofReal (D.vol V) := by
  rw [muQ_univ]
  exact mass_eq_of_isVolPair h V hs (volPair_isVolPair V (isVolPair_of_volTie h V hs))

/- English proof (translation)
Use `show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤`. Rewrite using `[muQ_univ_eq_vol h V hs]`. Conclude with `⟨(ENNReal.ofReal_pos.mpr (D.vol_pos V)).ne', ENNReal.ofReal_ne_top⟩`.
-/
theorem finVol_of_volTie (h : VolTieG D) (V : HSp D) (hs : V.SigOK) : FinVol V := by
  show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤
  rw [muQ_univ_eq_vol h V hs]
  exact ⟨(ENNReal.ofReal_pos.mpr (D.vol_pos V)).ne', ENNReal.ofReal_ne_top⟩

/- English proof (translation)
The claim follows from `finVol_of_volTie h _ (D.sp.W_sig j)`.
-/
theorem finVol_alt (h : VolTieG D) (j : ℕ) : FinVol (D.sp.W j) := finVol_of_volTie h _ (D.sp.W_sig j)

/- English proof (translation)
Substitute `hV` using the available equality. Conclude with `finVol_alt h j`.
-/
theorem finVol_of_eqW (h : VolTieG D) {V : HSp D} {j : ℕ} (hV : V = D.sp.W j) : FinVol V := by
  subst hV
  exact finVol_alt h j

/- English proof (translation)
Establish `hf : muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤` using `finVol_of_volTie h V hs`. Unfold `muQ1`. Rewrite using `[if_pos hf, muQ_univ_eq_vol h V hs]`.
-/
theorem normalized_quotient_measure_eq (h : VolTieG D) (V : HSp D) (hs : V.SigOK) :
    muQ1 V = (ENNReal.ofReal (D.vol V))⁻¹ • muQ V := by
  have hf : muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ := finVol_of_volTie h V hs
  unfold muQ1
  rw [if_pos hf, muQ_univ_eq_vol h V hs]

/- English proof (translation)
Rewrite using `[normalized_quotient_measure_eq h V hs]`. Both sides reduce to the same expression.
-/
theorem probability_measure_eq_pair (h : VolTieG D) (V : HSp D) (hs : V.SigOK) :
    muQ1 V = (ENNReal.ofReal (D.vol V))⁻¹ • (((volPair V).1.restrict (volPair V).2).map (autMk V)) := by
  rw [normalized_quotient_measure_eq h V hs]
  rfl

end Formalism.L2.Pj
