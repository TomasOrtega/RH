import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps h0 h1 C hC`. Take `⟨a1, ha1⟩` from `hP eps h0 h1 C hC`. Take `⟨b1, hb1⟩` from `hQ eps h0 h1 C hC`. Use `⟨max a1 b1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨a2, ha2⟩` from `ha1 cD (le_trans (le_max_left _ _) hcD)`.

Take `⟨b2, hb2⟩` from `hb1 cD (le_trans (le_max_right _ _) hcD)`. Use `⟨max a2 b2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨a3, ha3⟩` from `ha2 ch (le_trans (le_max_left _ _) hch)`. Take `⟨b3, hb3⟩` from `hb2 ch (le_trans (le_max_right _ _) hch)`. Use `⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `ha3 D L he (le_trans (le_max_left _ _) hx) hV`. Conclude with `hb3 D L he (le_trans (le_max_right _ _) hx) hV`.
-/
theorem SzRow.and {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P) (hQ : SzRow Q) :
    SzRow (fun C D L => P C D L ∧ Q C D L) := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  obtain ⟨b1, hb1⟩ := hQ eps h0 h1 C hC
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  refine ⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩
  · exact ha3 D L he (le_trans (le_max_left _ _) hx) hV
  · exact hb3 D L he (le_trans (le_max_right _ _) hx) hV

/- English proof (translation)
Introduce `eps h0 h1 C hC`. Take `⟨a1, ha1⟩` from `hP eps h0 h1 C hC`. Use `⟨a1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨a2, ha2⟩` from `ha1 cD hcD`. Use `⟨a2, fun ch hch => ?_⟩` and prove the remaining obligations.

Take `⟨a3, ha3⟩` from `ha2 ch hch`. Conclude with `⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩`.
-/
theorem SzRow.imp {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P)
    (h : ∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) : SzRow Q := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩`.
-/
theorem szRow_and_imp :
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P → SzRow Q → SzRow (fun C D L => P C D L ∧ Q C D L)) ∧
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P →
      (∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) → SzRow Q) :=
  ⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩

end GlobalTheory.EX
