import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩, ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc), fun …`.
-/
theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

/- English proof (translation)
Take `⟨a, ha, hp⟩` from `hp`. Take `⟨b, hb, hq⟩` from `hq`. Use `⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hp e C8 he (hle.trans (min_le_left _ _)) h52 h8`. Take `⟨K', hK'⟩` from `hq e C8 he (hle.trans (min_le_right _ _)) h52 h8`.

Use `⟨K.sup K', fun C hC hC8 hL => ?_⟩` and prove the remaining obligations. Take `⟨a1, ha1⟩` from `hK C hC hC8 (fc_large_of_sup hL).1`. Take `⟨b1, hb1⟩` from `hK' C hC hC8 (fc_large_of_sup hL).2`. Use `⟨max a1 b1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨a2, ha2⟩` from `ha1 cD (le_trans (le_max_left _ _) hcD)`.

Take `⟨b2, hb2⟩` from `hb1 cD (le_trans (le_max_right _ _) hcD)`. Use `⟨max a2 b2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨a3, ha3⟩` from `ha2 ch (le_trans (le_max_left _ _) hch)`. Take `⟨b3, hb3⟩` from `hb2 ch (le_trans (le_max_right _ _) hch)`. Conclude with `⟨max a3 b3, fun X h1 h2 h3 h4 hx => ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩`.
-/
theorem Ev.and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (fc_large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (fc_large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

/- English proof (translation)
Take `⟨a, ha, hp⟩` from `hp`. Use `⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hp e C8 he hle h52 h8`. Use `⟨K, fun C hC hC8 hL => ?_⟩` and prove the remaining obligations. Take `⟨a1, ha1⟩` from `hK C hC hC8 hL`.

Use `⟨a1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨a2, ha2⟩` from `ha1 cD hcD`. Use `⟨a2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨a3, ha3⟩` from `ha2 ch hch`. Conclude with `⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩`.
-/
theorem Ev.mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

/- English proof (translation)
The claim follows from `large₂.inter hp hq`.
-/
theorem large₂.and {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  large₂.inter hp hq

/- English proof (translation)
The claim follows from `large₂.imp hp h`.
-/
theorem large₂.mono {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop}
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) (hp : large₂ K p) : large₂ K q :=
  large₂.imp hp h

end GlobalTheory.Mem.Top
